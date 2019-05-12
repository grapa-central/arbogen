module type Sig =
sig
  val name : string
  val init : int -> unit
  val self_init : unit -> unit
  val int : int -> int
  val float : float -> float
  val get_state : unit -> Random.State.t
  val set_state : Random.State.t -> unit
end

module OcamlRandom : Sig =
struct
  let name = "ocaml"
  let init = Random.init
  let self_init = Random.self_init
  let int = Random.int
  let float = Random.float
  let get_state = Random.get_state
  let set_state = Random.set_state
end

module Randu : Sig =
struct
  let name = "randu"
  let state = ref 3
  let max_mod = 2 lsl 31
  let max_mod_f = float_of_int max_mod

  type random_state_t = { st : int array; mutable idx : int }

  let init n = state := n

  let self_init () = Random.self_init (); state := Random.int (2 lsl 20)

  let int n =
    let r = ((65539 * !state ) mod max_mod) in
    state := r;
    r mod n

  let float f =
    let n = (int max_mod) in
    state := n;
    f *. ((float_of_int n) /. max_mod_f)

  let get_state () = Obj.magic { st = Array.make 55 0; idx = !state }

  let set_state s =
    let { st = _ ; idx = n} = Obj.magic s in
    state := n
end

module RandNull : Sig =
struct
  let name = "randnull"
  let state = ref 0
  let max_mod = 1000
  let l = [|90; 27; 757; 338; 760; 84; 865; 310; 949; 161; 404; 696;
            243; 739; 380; 459; 4; 340; 658; 305; 22; 749; 53; 938;
            793; 225; 819; 236; 32; 333; 677; 753; 68; 520; 215; 624;
            449; 443; 400; 51; 971; 541; 521; 620; 130; 716; 87; 26;
            887; 863; 242; 747; 581; 267; 312; 856; 256; 12; 674; 826;
            808; 582; 635; 959; 810; 627; 602; 596; 803; 343; 850; 125;
            77; 861; 415; 104; 292; 990; 482; 574; 272; 636; 158;
            691; 606; 532; 204; 446; 136; 972; 708; 369; 556; 552; 124;
            742; 598; 156; 210; 778; 148; 21; 929; 183; 19; 494; 897;
            108; 159; 777; 485; 672; 862; 509; 376; 896; 444; 252;
            378; 628; 436; 518; 585; 682; 720; 160; 639; 569; 138; 67;
            96; 814; 166; 273; 604; 707; 427; 647; 944; 907; 394; 41;
            254; 432; 370; 931; 346; 155; 384; 558; 712; 115; 223; 855;
            787; 497; 452; 772; 992; 886; 259; 122; 756; 316; 385;
            293; 650; 748; 956; 547; 709; 245; 744; 74; 402; 734; 235;
            925; 419; 260; 617; 873; 503; 851; 507; 586; 893; 505; 643;
            417; 798; 123; 858; 989; 119; 45; 336; 46; 50; 522; 107;
            306; 291; 134; 563; 957; 154; 669; 513; 979; 13; 430; 611;
            844; 695; 314; 109; 773; 458; 775; 476; 791; 356; 597; 781;
            6; 878; 888; 750; 538; 641; 529; 687; 29; 462; 864; 654;
            655; 474; 950; 287; 322; 383; 948; 790; 416; 615; 980; 275;
            769; 42; 341; 288; 227; 872; 849; 327; 651; 663; 921;
            592; 933; 725; 101; 216; 405; 368; 523; 782; 736; 679; 998;
            815; 499; 824; 767; 914; 941; 630; 1; 164; 900; 960; 905;
            528; 668; 894; 483; 568; 536; 671; 290; 847; 261; 524;
            738; 8; 129; 885; 666; 173; 975; 307; 963; 177; 135; 30;
            762; 713; 550; 414; 922; 908; 883; 412; 692; 703; 584; 319;
            576; 361; 397; 601; 351; 665; 377; 128; 754; 926; 591;
            890; 561; 222; 608; 269; 331; 143; 535; 752; 329; 289; 761;
            342; 345; 420; 226; 241; 947; 422; 577; 965; 583; 207;
            367; 278; 765; 70; 106; 901; 974; 296; 467; 805; 463; 137;
            325; 317; 2; 827; 629; 472; 33; 845; 768; 930; 406; 848;
            121; 85; 457; 539; 47; 442; 373; 212; 224; 802; 958; 869;
            98; 3; 699; 141; 61; 800; 232; 565; 320; 910; 321; 163;
            570; 196; 358; 955; 238; 100; 646; 928; 578; 726; 391; 498;
            843; 644; 995; 895; 670; 986; 5; 846; 190; 309; 951; 448;
            675; 221; 330; 95; 469; 564; 867; 688; 710; 978; 202;
            172; 263; 728; 220; 496; 286; 318; 250; 398; 599; 912; 891;
            295; 300; 365; 201; 562; 706; 923; 623; 899; 732; 408;
            689; 339; 701; 870; 763; 614; 943; 403; 297; 939; 525; 389;
            169; 502; 65; 117; 797; 913; 151; 587; 441; 548; 189;
            838; 924; 434; 834; 976; 473; 920; 83; 251; 344; 719; 813;
            179; 660; 214; 206; 311; 758; 62; 812; 193; 279; 816; 714;
            423; 335; 379; 776; 387; 435; 717; 355; 233; 741; 506; 57;
            545; 78; 116; 771; 88; 796; 20; 99; 31; 618; 465; 526; 966;
            447; 993; 904; 832; 167; 71; 607; 280; 438; 649; 139;
            622; 11; 302; 673; 879; 145; 81; 514; 580; 531; 854; 268;
            559; 952; 544; 399; 764; 409; 804; 715; 985; 779; 213; 994;
            936; 969; 911; 73; 661; 852; 940; 553; 460; 537; 93; 915;
            439; 455; 120; 723; 573; 431; 877; 795; 836; 631; 200;
            511; 388; 554; 737; 676; 91; 489; 830; 946; 382; 868; 637;
            495; 150; 681; 428; 935; 113; 751; 902; 866; 199; 258; 745;
            840; 334; 10; 392; 308; 82; 662; 246; 982; 837; 988; 332;
            253; 277; 149; 59; 743; 549; 348; 609; 410; 766; 731;
            519; 579; 262; 575; 304; 15; 684; 265; 470; 466; 371; 996;
            337; 884; 491; 626; 34; 780; 889; 248; 859; 38; 208; 357;
            680; 638; 418; 981; 829; 324; 197; 205; 171; 234; 315; 987;
            527; 170; 517; 678; 916; 453; 652; 374; 23; 880; 168;
            299; 600; 711; 247; 16; 917; 909; 789; 605; 657; 44; 882;
            876; 515; 454; 730; 360; 792; 285; 450; 86; 871; 705; 881;
            733; 157; 542; 501; 683; 76; 821; 686; 937; 999; 694; 724;
            237; 353; 127; 942; 774; 165; 425; 642; 366; 231; 112; 984;
            718; 659; 0; 94; 97; 492; 464; 49; 182; 131; 451; 488;
            964; 954; 55; 386; 195; 625; 209; 478; 105; 839; 534; 40;
            828; 303; 919; 613; 229; 727; 759; 176; 927; 175; 79; 857;
            395; 934; 192; 806; 218; 363; 693; 817; 187; 244; 188; 589;
            786; 685; 479; 842; 484; 590; 7; 219; 634; 203; 401; 132;
            52; 249; 153; 424; 456; 874; 853; 413; 906; 977; 294;
            326; 14; 69; 656; 475; 697; 560; 546; 898; 35; 481; 36;
            557; 970; 704; 825; 217; 396; 198; 997; 230; 603; 860; 822;
            510; 140; 283; 276; 967; 746; 594; 735; 323; 133; 530;
            274; 174; 645; 721; 390; 477; 75; 362; 504; 755; 25; 807;
            186; 892; 146; 178; 349; 973; 181; 612; 500; 194; 440; 56;
            633; 493; 566; 667; 621; 185; 571; 740; 375; 875; 437; 516;
            58; 126; 111; 191; 648; 180; 328; 80; 783; 255; 393; 72;
            468; 313; 103; 92; 480; 640; 799; 595; 811; 350; 152; 144;
            239; 114; 17; 953; 983; 429; 24; 28; 162; 702; 426; 543;
            184; 619; 540; 147; 588; 282; 54; 9; 770; 228; 833; 945;
            118; 551; 142; 240; 66; 284; 352; 110; 461; 63; 788; 281;
            616; 407; 823; 572; 43; 690; 610; 809; 508; 266; 271; 841;
            784; 257; 298; 64; 918; 632; 835; 264; 820; 831; 421; 903;
            347; 48; 381; 102; 486; 411; 354; 490; 37; 60; 961; 785;
            794; 359; 932; 700; 801; 270; 533; 301; 818; 653; 991; 567;
            968; 555; 729; 722; 89; 664; 593; 445; 211; 471; 18; 372;
            962; 487; 433; 39; 512; 698; 364|]


  let max_mod_f = float_of_int max_mod

  type random_state_t = { st : int array; mutable idx : int }

  let init n = state := n mod max_mod

  let self_init () =  Random.self_init (); state := Random.int 100

  let int _ =
    let i = !state in
    state := (!state + 1) mod max_mod;
    l.(i)

  let float f =
    let n = (int max_mod) in
    let r = f *. ((float_of_int n) /. max_mod_f) in
    r

  let get_state () = Obj.magic { st = Array.make 55 0; idx = !state }

  let set_state s =
    let { st = _ ; idx = n} = Obj.magic s in
    state := n
end

let all_rand_gens = [
  OcamlRandom.name, (module OcamlRandom: Sig);
  Randu.name, (module Randu: Sig);
  RandNull.name, (module RandNull: Sig);
]

let get name = List.assoc name all_rand_gens
