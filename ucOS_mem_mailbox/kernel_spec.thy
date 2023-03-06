theory kernel_spec
imports Main Heap "../picore_SIMP_lemma" 
begin

section \<open>data types and state\<close>
typedecl Thread
typedecl Message

typedef mailbox_ref = ref by (simp add: ref_def)
typedef OS_MEM_ref = ref by (simp add: ref_def)

text\<open> we define memory address as nat \<close>
type_synonym mem_ref = nat

abbreviation "NULL \<equiv> 0 :: nat"

text\<open> we have a thread scheduler, thread has 3 types. BLOCKED means a thread is waiting for memory and is in wait queue \<close>
datatype Thread_State_Type = READY | RUNNING | BLOCKED

text\<open>OS_MEM is Memory control block of ucOS
     OSMemAddr points to beginning of memory partition;
     OSMemFreeList is a list of pointers that points to free memory blocks
     OSMemBlkSize is the size of each block of memory
     OSMemNBlks is the total number of blocks in this partition
     OSMemFree is the number of free blocks remaining\<close>

record OS_MEM = OSMemAddr :: mem_ref
                OSMemFreeList :: "mem_ref list"
                OSMemBlkSize :: int
                OSMemNBlks :: int
                OSMemNFree :: int

record Mail_box = buf :: mailbox_ref           (* head address of the mailbox *)
       msgPtr ::"Message option"               (* points to the message, it could be a None*)
       wait_q :: "Thread list"                 (* Group for wait list*)

record State = 
  (* threads and info *)
  cur :: "Thread option"
  tick :: nat
  OSMailBoxs :: "mailbox_ref  set"
  OSMailbox_info :: "mailbox_ref \<Rightarrow> Mail_box"
  thd_state :: "Thread \<Rightarrow> Thread_State_Type"
  (* all mem pools *) 
  OS_MEMs :: "OS_MEM_ref set"
  (* mem control block *)
  OS_MEM_info :: "OS_MEM_ref \<Rightarrow> OS_MEM"
  (* local variable for threads *)
  ret :: "Thread \<Rightarrow> int"
  ret_mem :: "Thread \<Rightarrow> mem_ref option"
  tmout :: "Thread \<Rightarrow> int"
  endt :: "Thread \<Rightarrow> nat "
  posting_msg ::"Thread \<Rightarrow> Message"
  get_msg :: "Thread \<Rightarrow> Message option"       (*If the mailbox if empty, it will get a NULL*)
  th :: "Thread \<Rightarrow> Thread"
  need_resched :: "Thread \<Rightarrow> bool"
  statPend :: "Thread \<Rightarrow> int"

text \<open> Parameter for mailbox \<close>
abbreviation "FOREVER \<equiv> (-1)::int"
abbreviation "NOWAIT \<equiv> 0::int"

text \<open> ERROR CODE for mem syscalls \<close>
abbreviation "OS_ERR_MEM_INVALID_ADDR \<equiv> (-1)::int"
abbreviation "OS_ERR_MEM_INVALID_BLKS \<equiv> (-2)::int"
abbreviation "OS_ERR_MEM_INVALID_SIZE \<equiv> (-3)::int"
abbreviation "OS_ERR_MEM_INVALID_PART \<equiv> (-4)::int"
abbreviation "OS_ERR_MEM_NO_FREE_BLKS \<equiv> (-5)::int"
abbreviation "OS_ERR_MEM_FULL \<equiv> (-6)::int"
abbreviation "OS_MEM_FULL \<equiv> (-7) :: int"
abbreviation "OS_ERR_NONE \<equiv> 0 :: int"

text \<open> ERROR CODE for mailbox syscalls \<close>
abbreviation "OS_ERR_PEVENT_NULL \<equiv> (-1)::int"
abbreviation "OS_ERR_EVENT_TYPE \<equiv> (-2)::int"
abbreviation "OS_ERR_PEND_ISR \<equiv> (-3)::int"
abbreviation "OS_ERR_PEND_LOCKED \<equiv> (-4)::int"
abbreviation "OS_ERR_TIMEOUT \<equiv> (-5)::int"
abbreviation "OS_ERR_MBOX_FULL \<equiv> (-6)::int"
abbreviation "OS_ERR_POST_NULL_PTR \<equiv> -7::int"
abbreviation "OS_STAT_PEND_OK \<equiv> (-14)::int"
abbreviation "OS_STAT_PEND_ABORT \<equiv> -13::int"

abbreviation "ETIMEOUT \<equiv> (-1) :: int"

section \<open>specification of events\<close>
datatype Core = \<S> | \<T> Thread | Timer

text\<open>labels for different events\<close>
datatype EL = ScheduleE | TickE | OSMemPutE | OSMemGetE | OSMemCreateE 
              | OSMboxPostE | OSMboxPendE | OSMboxAcceptE

text\<open>data types for event parameters\<close>
datatype Parameter = Thread Thread | NBlks int | BlkSize int | PMem OS_MEM_ref | PBlk mem_ref 
                     | Addr mem_ref | MBRef mailbox_ref | Msg "Message option" | Integer int

type_synonym EventLabel = "EL \<times> (Parameter list \<times> Core)" 

definition get_evt_label :: "EL \<Rightarrow> Parameter list \<Rightarrow> Core \<Rightarrow> EventLabel" ("_ _ \<Rrightarrow> _" [30,30,30] 20)
  where "get_evt_label el ps k \<equiv> (el,(ps,k))"

definition stm :: "Thread \<Rightarrow> State com \<Rightarrow> State com" ("_ \<^enum> _" [0,0] 21)
  where "stm t p = AWAIT \<acute>cur = Some t THEN p END"

text\<open>
 \<mu>c/OS-II uses two events: reschedule for free and swap for alloc for context switch
\<close>
definition reschedule :: "State com"
where "reschedule \<equiv> 
  \<acute>thd_state := \<acute>thd_state(the \<acute>cur := READY);;
  \<acute>cur := Some (SOME t. \<acute>thd_state t = READY);;
  \<acute>thd_state := \<acute>thd_state(the \<acute>cur := RUNNING)"


definition swap :: "State com"
where "swap \<equiv> 
  IF (\<exists>t. \<acute>thd_state t = READY) THEN
    \<acute>cur := Some (SOME t. \<acute>thd_state t = READY);;
    \<acute>thd_state := \<acute>thd_state(the \<acute>cur := RUNNING)
  ELSE
    \<acute>cur := None
  FI"

subsection \<open>specification of events\<close>

definition Tick :: "(EventLabel, Core, State, State com option) event" 
where "Tick \<equiv> 
  EVENT TickE [] \<Rrightarrow> Timer
  THEN 
    \<acute>tick := \<acute>tick + 1
  END"

definition Schedule :: "Thread \<Rightarrow> (EventLabel, Core, State, State com option) event" 
where "Schedule t \<equiv> 
  EVENT ScheduleE [Thread t] \<Rrightarrow> \<S> 
  THEN 
    AWAIT \<acute>thd_state t = READY THEN  (* only schedule the READY threads *)
      IF (\<acute>cur \<noteq> None) THEN 
        \<acute>thd_state := \<acute>thd_state(the (\<acute>cur) := READY);;
        \<acute>cur := None
      FI;;
      \<acute>cur := Some t;;
      \<acute>thd_state := \<acute>thd_state(t := RUNNING)
    END
  END"

definition OSMemGet :: "Thread \<Rightarrow> OS_MEM_ref \<Rightarrow> (EventLabel, Core, State, State com option) event"
  where "OSMemGet t pmem \<equiv>
  EVENT OSMemGetE [PMem pmem] \<Rrightarrow> (\<T> t)
  WHEN
    pmem \<in> \<acute>OS_MEMs
  THEN
     t \<^enum> \<acute>ret_mem := \<acute>ret_mem(t := None) ;;
    (t \<^enum> ATOMIC 
       IF OSMemNFree (\<acute>OS_MEM_info pmem) > 0 THEN
        \<acute>ret_mem := \<acute>ret_mem(t := Some (hd (OSMemFreeList (\<acute>OS_MEM_info pmem)))) ;;
         \<acute>OS_MEM_info := \<acute>OS_MEM_info(pmem := (\<acute>OS_MEM_info pmem) \<lparr> OSMemFreeList := tl (OSMemFreeList (\<acute>OS_MEM_info pmem)) \<rparr>);;
         \<acute>OS_MEM_info := \<acute>OS_MEM_info(pmem := (\<acute>OS_MEM_info pmem) \<lparr> OSMemNFree := OSMemNFree (\<acute>OS_MEM_info pmem) - 1 \<rparr>);;
         \<acute>ret := \<acute>ret(t := OS_ERR_NONE)
       ELSE
         \<acute>ret := \<acute>ret (t := OS_ERR_MEM_NO_FREE_BLKS)
       FI
    END)
  END
"

definition OSMemPut :: "Thread \<Rightarrow> OS_MEM_ref \<Rightarrow> mem_ref \<Rightarrow> (EventLabel, Core, State, State com option) event" 
where "OSMemPut t pmem pblk \<equiv> 
  EVENT OSMemPutE [PMem pmem, PBlk pblk] \<Rrightarrow> (\<T> t)
  WHEN 
    pmem \<in> \<acute>OS_MEMs
  THEN 
    (t \<^enum> ATOMIC
      IF OSMemNFree (\<acute>OS_MEM_info pmem) \<ge>  OSMemNBlks (\<acute>OS_MEM_info pmem) THEN
        \<acute>ret := \<acute>ret (t := OS_MEM_FULL)
      ELSE
        \<acute>OS_MEM_info := \<acute>OS_MEM_info(pmem := (\<acute>OS_MEM_info pmem) \<lparr> OSMemFreeList := [pblk] @ OSMemFreeList (\<acute>OS_MEM_info pmem) \<rparr>) ;;
        \<acute>OS_MEM_info := \<acute>OS_MEM_info(pmem := (\<acute>OS_MEM_info pmem) \<lparr> OSMemNFree := OSMemNFree (\<acute>OS_MEM_info pmem) + 1 \<rparr>) ;; 
        \<acute>ret := \<acute>ret (t := OS_ERR_NONE)
      FI
    END)
  END"

definition OSMboxPend :: "Thread \<Rightarrow> mailbox_ref \<Rightarrow> int \<Rightarrow> (EventLabel, Core, State, State com option) event"
  where "OSMboxPend t pevent timeout =
    EVENT OSMboxPendE [MBRef pevent, Integer timeout] \<Rrightarrow> (\<T> t)
    WHEN 
         pevent \<in> \<acute>OSMailBoxs   (*( \<and> timeout \<ge> -1*)    \<comment> \<open>  equv to (timeout = FOREVER \<or> timeout = NOWAIT \<or> timeout > 0) 
                                                       (* \<and> p \<in> \<acute>pools_of_thread t *) (* the mem pool p is shared in the thread t   \<close>
    THEN
        (t \<^enum> \<acute>tmout := \<acute>tmout(t := timeout));;
        (t \<^enum> \<acute>endt := \<acute>endt(t := 0));;
        (t \<^enum> IF timeout > 0 THEN 
               \<acute>endt := \<acute>endt(t := \<acute>tick + nat timeout)   \<comment> \<open>  calculate the end time for timeout \<close>
         FI);;
       (* \<acute>tick := \<acute>tick + 1;;*)

        (t \<^enum> \<acute>ret := \<acute>ret(t := OS_ERR_PEVENT_NULL));;      \<comment> \<open> initialize local vars \<close>
        (t \<^enum> \<acute>statPend := \<acute>statPend(t := OS_STAT_PEND_OK));; 
    
        (t \<^enum> IF pevent \<notin> \<acute>OSMailBoxs THEN 
             \<acute>ret := \<acute>ret(t := OS_ERR_PEVENT_NULL)
         ELSE
             IF msgPtr(\<acute>OSMailbox_info pevent) \<noteq> None THEN                                           \<comment> \<open>pmsg = pevent->OSEventPtr   if pmsg != (void *)0  \<close>
                (\<acute>get_msg := \<acute>get_msg(t := msgPtr (\<acute>OSMailbox_info pevent)));;                                 \<comment> \<open>return pmsg \<close>
                (\<acute>ret := \<acute>ret(t := OS_ERR_NONE));;                                                             \<comment> \<open>*perr = OS_ERR_NONE \<close>
             (t \<^enum> (\<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent :=  (\<acute>OSMailbox_info pevent)\<lparr>msgPtr := None\<rparr>)))       \<comment> \<open> pevent\<rightarrow>OSEventPtr = (void *)0 \<close>
             ELSE 
                (t \<^enum> ATOMIC
                    \<acute>thd_state := \<acute>thd_state(the \<acute>cur := BLOCKED);;
                    \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := \<acute>OSMailbox_info pevent\<lparr>wait_q := wait_q (\<acute>OSMailbox_info pevent) @ [the \<acute>cur] \<rparr>);;
                    swap
                 END)
                (*skip*)  \<comment> \<open> Operations that deals with pending \<close>                                    
             FI
         FI);;
         
        (t \<^enum> ATOMIC
             IF \<acute>statPend t = OS_STAT_PEND_OK THEN
                \<acute>ret := \<acute>ret(t := OS_ERR_NONE)
             ELSE
                \<acute>ret := \<acute>ret(t := OS_ERR_TIMEOUT)    \<comment> \<open>lack a interrupt handler that can modify the statPend of thread t // OS_STAT_PEND_TIMEOUT  \<close>
             FI
        END);;
   
         IF \<acute>tmout t \<noteq> FOREVER THEN
            (t \<^enum> \<acute>tmout := \<acute>tmout (t := int (\<acute>endt t) - int \<acute>tick));;
            IF \<acute>tmout t < 0 THEN
              (t \<^enum> \<acute>ret := \<acute>ret (t := OS_ERR_TIMEOUT))
            FI
         FI
         
    END"

definition OSMboxPost :: "Thread \<Rightarrow> mailbox_ref \<Rightarrow> Message option \<Rightarrow> (EventLabel, Core, State, State com option) event"
  where "OSMboxPost t pevent msg =
    EVENT OSMboxPostE [MBRef pevent, Msg msg] \<Rrightarrow> (\<T> t)
    WHEN 
         pevent \<in> \<acute>OSMailBoxs 
    THEN
       IF msg = None THEN
           (t \<^enum> \<acute>ret := \<acute>ret(t := OS_ERR_POST_NULL_PTR))
       ELSE
           (t \<^enum> ATOMIC
                IF  wait_q (\<acute>OSMailbox_info pevent) \<noteq> [] THEN 
                   \<acute>th := \<acute>th (t := hd (wait_q (\<acute>OSMailbox_info  pevent)));;

                    \<acute>tmout := \<acute>tmout(\<acute>th t := 0);;    
                    \<acute>get_msg :=\<acute>get_msg(\<acute>th t := msg);;   \<comment> \<open>send the msg to the task which is pending\<close>
                    \<acute>statPend := \<acute>statPend(\<acute>th t := OS_STAT_PEND_OK);;

                      (* _unpend_thread(th); *)
                   \<acute>OSMailbox_info := \<acute>OSMailbox_info (pevent := \<acute>OSMailbox_info pevent  \<lparr>wait_q := tl (wait_q (\<acute>OSMailbox_info pevent))\<rparr>);;
                      (* _ready_thread(th); *)
                   \<acute>thd_state := \<acute>thd_state (\<acute>th t := READY);;
                   \<acute>need_resched := \<acute>need_resched(t := True);;
                      
                    IF \<acute>need_resched t THEN  
                        reschedule             (*schedule t/swap or reschedule *)
                    FI;;
                   \<acute>ret := \<acute>ret(t := OS_ERR_NONE)
                ELSE
                   IF msgPtr(\<acute>OSMailbox_info pevent) \<noteq> None THEN
                      \<acute>ret := \<acute>ret(t := OS_ERR_MBOX_FULL)
                   ELSE
                      \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent :=  (\<acute>OSMailbox_info pevent)\<lparr>msgPtr := msg\<rparr>);;
                      \<acute>ret := \<acute>ret(t := OS_ERR_NONE)
                   FI
              FI
          END)
       FI
    END"


definition OSMboxAccept :: "Thread \<Rightarrow> mailbox_ref  \<Rightarrow> (EventLabel, Core, State, State com option) event"
  where "OSMboxAccept t pevent =
    EVENT OSMboxAcceptE [MBRef pevent] \<Rrightarrow> (\<T> t)
    WHEN 
         pevent \<in> \<acute>OSMailBoxs 
    THEN
        (t \<^enum> ATOMIC
          \<acute>get_msg := \<acute>get_msg(t := msgPtr (\<acute>OSMailbox_info pevent));;                              \<comment> \<open>The thread which invoked the task get the message contained in the corresponding mailbx           \<close> 
          \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent :=  (\<acute>OSMailbox_info pevent)\<lparr>msgPtr := None\<rparr>)    \<comment> \<open>clear the mailbox\<close>
        END)
    END"

end

