From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [src/check-pkvm-pgtables.c]. *)
Section code.
  Definition file_0 : string := "src/check-pkvm-pgtables.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 8 100 9.
  Definition loc_3 : location_info := LocationInfo file_0 63 22 100 9.
  Definition loc_4 : location_info := LocationInfo file_0 63 23 86 9.
  Definition loc_6 : location_info := LocationInfo file_0 64 15 86 9.
  Definition loc_8 : location_info := LocationInfo file_0 65 15 86 9.
  Definition loc_10 : location_info := LocationInfo file_0 67 8 86 9.
  Definition loc_11 : location_info := LocationInfo file_0 68 16 85 17.
  Definition loc_12 : location_info := LocationInfo file_0 86 9 96 17.
  Definition loc_14 : location_info := LocationInfo file_0 88 16 96 17.
  Definition loc_15 : location_info := LocationInfo file_0 96 17 99 32.
  Definition loc_17 : location_info := LocationInfo file_0 99 16 99 32.
  Definition loc_18 : location_info := LocationInfo file_0 99 23 99 31.
  Definition loc_19 : location_info := LocationInfo file_0 88 84 96 17.
  Definition loc_20 : location_info := LocationInfo file_0 88 85 91 42.
  Definition loc_22 : location_info := LocationInfo file_0 89 23 91 42.
  Definition loc_24 : location_info := LocationInfo file_0 91 24 91 42.
  Definition loc_25 : location_info := LocationInfo file_0 91 42 93 43.
  Definition loc_27 : location_info := LocationInfo file_0 93 24 93 43.
  Definition loc_28 : location_info := LocationInfo file_0 93 43 95 50.
  Definition loc_30 : location_info := LocationInfo file_0 95 24 95 50.
  Definition loc_31 : location_info := LocationInfo file_0 95 31 95 49.
  Definition loc_32 : location_info := LocationInfo file_0 93 31 93 42.
  Definition loc_33 : location_info := LocationInfo file_0 91 31 91 41.
  Definition loc_34 : location_info := LocationInfo file_0 88 24 88 82.
  Definition loc_35 : location_info := LocationInfo file_0 88 24 88 27.
  Definition loc_36 : location_info := LocationInfo file_0 88 24 88 27.
  Definition loc_37 : location_info := LocationInfo file_0 88 30 88 82.
  Definition loc_38 : location_info := LocationInfo file_0 88 32 88 55.
  Definition loc_39 : location_info := LocationInfo file_0 88 33 88 50.
  Definition loc_40 : location_info := LocationInfo file_0 88 33 88 37.
  Definition loc_41 : location_info := LocationInfo file_0 88 35 88 36.
  Definition loc_42 : location_info := LocationInfo file_0 88 40 88 50.
  Definition loc_43 : location_info := LocationInfo file_0 88 41 88 42.
  Definition loc_44 : location_info := LocationInfo file_0 88 46 88 49.
  Definition loc_45 : location_info := LocationInfo file_0 88 53 88 54.
  Definition loc_46 : location_info := LocationInfo file_0 88 58 88 80.
  Definition loc_47 : location_info := LocationInfo file_0 88 59 88 61.
  Definition loc_48 : location_info := LocationInfo file_0 88 60 88 61.
  Definition loc_49 : location_info := LocationInfo file_0 88 65 88 79.
  Definition loc_50 : location_info := LocationInfo file_0 88 66 88 72.
  Definition loc_51 : location_info := LocationInfo file_0 88 66 88 68.
  Definition loc_52 : location_info := LocationInfo file_0 88 71 88 72.
  Definition loc_53 : location_info := LocationInfo file_0 88 75 88 78.
  Definition loc_54 : location_info := LocationInfo file_0 68 84 85 17.
  Definition loc_55 : location_info := LocationInfo file_0 68 85 71 42.
  Definition loc_57 : location_info := LocationInfo file_0 69 23 71 42.
  Definition loc_59 : location_info := LocationInfo file_0 71 24 71 42.
  Definition loc_60 : location_info := LocationInfo file_0 71 42 80 25.
  Definition loc_62 : location_info := LocationInfo file_0 73 24 80 25.
  Definition loc_63 : location_info := LocationInfo file_0 80 25 82 40.
  Definition loc_65 : location_info := LocationInfo file_0 82 24 82 40.
  Definition loc_66 : location_info := LocationInfo file_0 82 40 84 40.
  Definition loc_68 : location_info := LocationInfo file_0 84 24 84 40.
  Definition loc_69 : location_info := LocationInfo file_0 84 31 84 39.
  Definition loc_70 : location_info := LocationInfo file_0 82 31 82 39.
  Definition loc_71 : location_info := LocationInfo file_0 74 24 80 25.
  Definition loc_72 : location_info := LocationInfo file_0 74 25 76 62.
  Definition loc_74 : location_info := LocationInfo file_0 76 32 76 62.
  Definition loc_75 : location_info := LocationInfo file_0 76 62 79 48.
  Definition loc_77 : location_info := LocationInfo file_0 77 31 79 48.
  Definition loc_79 : location_info := LocationInfo file_0 79 32 79 48.
  Definition loc_80 : location_info := LocationInfo file_0 79 39 79 47.
  Definition loc_81 : location_info := LocationInfo file_0 76 39 76 61.
  Definition loc_82 : location_info := LocationInfo file_0 73 32 73 37.
  Definition loc_83 : location_info := LocationInfo file_0 73 32 73 37.
  Definition loc_84 : location_info := LocationInfo file_0 71 31 71 41.
  Definition loc_85 : location_info := LocationInfo file_0 68 24 68 82.
  Definition loc_86 : location_info := LocationInfo file_0 68 24 68 27.
  Definition loc_87 : location_info := LocationInfo file_0 68 24 68 27.
  Definition loc_88 : location_info := LocationInfo file_0 68 30 68 82.
  Definition loc_89 : location_info := LocationInfo file_0 68 32 68 55.
  Definition loc_90 : location_info := LocationInfo file_0 68 33 68 50.
  Definition loc_91 : location_info := LocationInfo file_0 68 33 68 37.
  Definition loc_92 : location_info := LocationInfo file_0 68 35 68 36.
  Definition loc_93 : location_info := LocationInfo file_0 68 40 68 50.
  Definition loc_94 : location_info := LocationInfo file_0 68 41 68 42.
  Definition loc_95 : location_info := LocationInfo file_0 68 46 68 49.
  Definition loc_96 : location_info := LocationInfo file_0 68 53 68 54.
  Definition loc_97 : location_info := LocationInfo file_0 68 58 68 80.
  Definition loc_98 : location_info := LocationInfo file_0 68 59 68 61.
  Definition loc_99 : location_info := LocationInfo file_0 68 60 68 61.
  Definition loc_100 : location_info := LocationInfo file_0 68 65 68 79.
  Definition loc_101 : location_info := LocationInfo file_0 68 66 68 72.
  Definition loc_102 : location_info := LocationInfo file_0 68 66 68 68.
  Definition loc_103 : location_info := LocationInfo file_0 68 71 68 72.
  Definition loc_104 : location_info := LocationInfo file_0 68 75 68 78.
  Definition loc_105 : location_info := LocationInfo file_0 63 15 63 20.
  Definition loc_106 : location_info := LocationInfo file_0 63 15 63 20.
  Definition loc_109 : location_info := LocationInfo file_0 107 2 107 11.
  Definition loc_110 : location_info := LocationInfo file_0 108 2 108 12.
  Definition loc_111 : location_info := LocationInfo file_0 110 2 110 46.
  Definition loc_112 : location_info := LocationInfo file_0 114 2 114 11.
  Definition loc_113 : location_info := LocationInfo file_0 114 9 114 10.
  Definition loc_114 : location_info := LocationInfo file_0 110 23 110 45.
  Definition loc_115 : location_info := LocationInfo file_0 110 23 110 33.
  Definition loc_116 : location_info := LocationInfo file_0 110 23 110 33.
  Definition loc_117 : location_info := LocationInfo file_0 110 34 110 37.
  Definition loc_118 : location_info := LocationInfo file_0 110 34 110 37.
  Definition loc_119 : location_info := LocationInfo file_0 110 39 110 44.
  Definition loc_120 : location_info := LocationInfo file_0 110 39 110 44.
  Definition loc_123 : location_info := LocationInfo file_0 108 2 108 7.
  Definition loc_124 : location_info := LocationInfo file_0 108 10 108 11.
  Definition loc_125 : location_info := LocationInfo file_0 107 2 107 5.
  Definition loc_126 : location_info := LocationInfo file_0 107 8 107 10.

  (* Definition of function [entry_kind]. *)
  Definition impl_entry_kind : function := {|
    f_args := [
      ("pte", it_layout u64);
      ("level", it_layout u8)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Switch u8
          (LocInfoE loc_105 (use{it_layout u8} (LocInfoE loc_106 ("level"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_4 ;
            Goto "#2") ::
            (locinfo: loc_6 ;
            Goto "#3") ::
            (locinfo: loc_8 ;
            Goto "#4") ::
            (locinfo: loc_12 ;
            Goto "#5") :: []
          )
          (locinfo: loc_15 ;
          Goto "#6")
      ]> $
      <[ "#1" :=
        Return (VOID)
      ]> $
      <[ "#11" :=
        locinfo: loc_22 ;
        Goto "#12"
      ]> $
      <[ "#12" :=
        locinfo: loc_24 ;
        Return (LocInfoE loc_33 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_33 (i2v 0 i32))))
      ]> $
      <[ "#13" :=
        locinfo: loc_27 ;
        Return (LocInfoE loc_32 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_32 (i2v 5 i32))))
      ]> $
      <[ "#14" :=
        locinfo: loc_30 ;
        Return (LocInfoE loc_31 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_31 (i2v 3 i32))))
      ]> $
      <[ "#15" :=
        locinfo: loc_15 ;
        Goto "#9"
      ]> $
      <[ "#17" :=
        locinfo: loc_57 ;
        Goto "#18"
      ]> $
      <[ "#18" :=
        locinfo: loc_59 ;
        Return (LocInfoE loc_84 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_84 (i2v 0 i32))))
      ]> $
      <[ "#19" :=
        locinfo: loc_62 ;
        Switch u8
          (LocInfoE loc_82 (use{it_layout u8} (LocInfoE loc_83 ("level"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> ∅
          )
          (
            (locinfo: loc_72 ;
            Goto "#25") ::
            (locinfo: loc_75 ;
            Goto "#26") ::
            (locinfo: loc_77 ;
            Goto "#27") :: []
          )
          (locinfo: loc_63 ;
          Goto "#22")
      ]> $
      <[ "#2" :=
        locinfo: loc_6 ;
        Goto "#3"
      ]> $
      <[ "#20" :=
        locinfo: loc_65 ;
        Return (LocInfoE loc_70 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_70 (i2v 2 i32))))
      ]> $
      <[ "#21" :=
        locinfo: loc_68 ;
        Return (LocInfoE loc_69 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_69 (i2v 6 i32))))
      ]> $
      <[ "#22" :=
        locinfo: loc_63 ;
        Goto "#20"
      ]> $
      <[ "#23" :=
        locinfo: loc_12 ;
        Goto "#7"
      ]> $
      <[ "#25" :=
        locinfo: loc_74 ;
        Return (LocInfoE loc_81 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_81 (i2v 4 i32))))
      ]> $
      <[ "#26" :=
        locinfo: loc_77 ;
        Goto "#27"
      ]> $
      <[ "#27" :=
        locinfo: loc_79 ;
        Return (LocInfoE loc_80 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_80 (i2v 1 i32))))
      ]> $
      <[ "#28" :=
        locinfo: loc_63 ;
        Goto "#22"
      ]> $
      <[ "#3" :=
        locinfo: loc_8 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_11 ;
        Switch u64
          (LocInfoE loc_85 ((LocInfoE loc_86 (use{it_layout u64} (LocInfoE loc_87 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_88 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_88 ((LocInfoE loc_89 ((LocInfoE loc_90 ((LocInfoE loc_91 (UnOp NotIntOp (IntOp i32) (LocInfoE loc_92 (i2v 0 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_93 ((LocInfoE loc_94 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_95 (i2v 0 i32)))))) +{IntOp i32, IntOp i32} (LocInfoE loc_96 (i2v 1 i32)))) &{IntOp i32, IntOp i32} (LocInfoE loc_97 ((LocInfoE loc_98 (UnOp NotIntOp (IntOp i32) (LocInfoE loc_99 (i2v 0 i32)))) >>{IntOp i32, IntOp i32} (LocInfoE loc_100 ((LocInfoE loc_101 ((LocInfoE loc_102 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_103 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_104 (i2v 1 i32))))))))))))
          (
            <[ 0 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_55 ;
            Goto "#17") ::
            (locinfo: loc_57 ;
            Goto "#18") ::
            (locinfo: loc_60 ;
            Goto "#19") ::
            (locinfo: loc_63 ;
            Goto "#20") :: []
          )
          (locinfo: loc_66 ;
          Goto "#21")
      ]> $
      <[ "#5" :=
        locinfo: loc_14 ;
        Switch u64
          (LocInfoE loc_34 ((LocInfoE loc_35 (use{it_layout u64} (LocInfoE loc_36 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_37 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_37 ((LocInfoE loc_38 ((LocInfoE loc_39 ((LocInfoE loc_40 (UnOp NotIntOp (IntOp i32) (LocInfoE loc_41 (i2v 0 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_42 ((LocInfoE loc_43 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_44 (i2v 0 i32)))))) +{IntOp i32, IntOp i32} (LocInfoE loc_45 (i2v 1 i32)))) &{IntOp i32, IntOp i32} (LocInfoE loc_46 ((LocInfoE loc_47 (UnOp NotIntOp (IntOp i32) (LocInfoE loc_48 (i2v 0 i32)))) >>{IntOp i32, IntOp i32} (LocInfoE loc_49 ((LocInfoE loc_50 ((LocInfoE loc_51 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_52 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_53 (i2v 1 i32))))))))))))
          (
            <[ 0 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_20 ;
            Goto "#11") ::
            (locinfo: loc_22 ;
            Goto "#12") ::
            (locinfo: loc_25 ;
            Goto "#13") ::
            (locinfo: loc_28 ;
            Goto "#14") :: []
          )
          (locinfo: loc_15 ;
          Goto "#9")
      ]> $
      <[ "#6" :=
        locinfo: loc_17 ;
        Return (LocInfoE loc_18 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_18 (i2v 6 i32))))
      ]> $
      <[ "#7" :=
        locinfo: loc_12 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        Goto "#1"
      ]> $
      <[ "#9" :=
        locinfo: loc_15 ;
        Goto "#6"
      ]> $∅
    )%E
  |}.

  (* Definition of function [main]. *)
  Definition impl_main (global_entry_kind : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("ek", it_layout u32);
      ("level", it_layout u8);
      ("pte", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_109 ;
        LocInfoE loc_125 ("pte") <-{ it_layout u64 }
          LocInfoE loc_126 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_126 (i2v 10 i32))) ;
        locinfo: loc_110 ;
        LocInfoE loc_123 ("level") <-{ it_layout u8 }
          LocInfoE loc_124 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_124 (i2v 3 i32))) ;
        "ek" <-{ it_layout u32 }
          LocInfoE loc_114 (Call (LocInfoE loc_116 (global_entry_kind)) [@{expr} LocInfoE loc_117 (use{it_layout u64} (LocInfoE loc_118 ("pte"))) ;
          LocInfoE loc_119 (use{it_layout u8} (LocInfoE loc_120 ("level"))) ]) ;
        locinfo: loc_112 ;
        Return (LocInfoE loc_113 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
