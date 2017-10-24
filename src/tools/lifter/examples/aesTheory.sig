signature aesTheory =
sig
  type thm = Thm.thm

  (*  Theorems  *)
    val aes_arm8_program_THM : thm
    val aes_m0_program_THM : thm

  val aes_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bir_inst_lifting] Parent theory of "aes"

   [aes_arm8_program_THM]  Theorem

       []
      |- bir_is_lifted_prog arm8_bmr (WI_end 0w 0x1000000w)
           [(0x400570w,
             [255w; 195w; 1w; 209w; 224w; 15w; 0w; 249w; 225w; 23w; 0w;
              185w; 226w; 7w; 0w; 249w; 227w; 3w; 0w; 249w; 224w; 23w; 64w;
              185w; 0w; 4w; 0w; 81w; 224w; 79w; 0w; 185w; 224w; 7w; 64w;
              249w; 0w; 0w; 64w; 185w; 224w; 47w; 0w; 185w; 224w; 7w; 64w;
              249w; 0w; 4w; 64w; 185w; 224w; 51w; 0w; 185w; 224w; 7w; 64w;
              249w; 0w; 8w; 64w; 185w; 224w; 55w; 0w; 185w; 224w; 7w; 64w;
              249w; 0w; 12w; 64w; 185w; 224w; 59w; 0w; 185w; 224w; 15w;
              64w; 249w; 0w; 0w; 64w; 185w; 225w; 47w; 64w; 185w; 32w; 0w;
              0w; 74w; 224w; 47w; 0w; 185w; 224w; 15w; 64w; 249w; 0w; 16w;
              0w; 145w; 0w; 0w; 64w; 185w; 225w; 51w; 64w; 185w; 32w; 0w;
              0w; 74w; 224w; 51w; 0w; 185w; 224w; 15w; 64w; 249w; 0w; 32w;
              0w; 145w; 0w; 0w; 64w; 185w; 225w; 55w; 64w; 185w; 32w; 0w;
              0w; 74w; 224w; 55w; 0w; 185w; 224w; 15w; 64w; 249w; 0w; 48w;
              0w; 145w; 0w; 0w; 64w; 185w; 225w; 59w; 64w; 185w; 32w; 0w;
              0w; 74w; 224w; 59w; 0w; 185w; 224w; 15w; 64w; 249w; 0w; 64w;
              0w; 145w; 224w; 15w; 0w; 249w; 230w; 0w; 0w; 20w; 224w; 47w;
              64w; 185w; 0w; 124w; 24w; 83w; 224w; 83w; 0w; 185w; 224w;
              51w; 64w; 185w; 0w; 124w; 16w; 83w; 0w; 28w; 0w; 18w; 224w;
              87w; 0w; 185w; 224w; 55w; 64w; 185w; 0w; 124w; 8w; 83w; 0w;
              28w; 0w; 18w; 224w; 91w; 0w; 185w; 224w; 59w; 64w; 185w; 0w;
              28w; 0w; 18w; 224w; 95w; 0w; 185w; 224w; 83w; 64w; 185w; 1w;
              244w; 126w; 211w; 0w; 0w; 0w; 144w; 0w; 64w; 57w; 145w; 32w;
              0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 99w; 0w; 185w; 224w;
              87w; 64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w; 176w; 0w;
              64w; 9w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w;
              103w; 0w; 185w; 224w; 91w; 64w; 185w; 1w; 244w; 126w; 211w;
              0w; 0w; 0w; 176w; 0w; 64w; 25w; 145w; 32w; 0w; 0w; 139w; 0w;
              0w; 64w; 185w; 224w; 107w; 0w; 185w; 224w; 95w; 64w; 185w;
              1w; 244w; 126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w; 41w; 145w;
              32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 111w; 0w; 185w;
              225w; 99w; 64w; 185w; 224w; 103w; 64w; 185w; 33w; 0w; 0w;
              74w; 224w; 107w; 64w; 185w; 33w; 0w; 0w; 74w; 224w; 111w;
              64w; 185w; 33w; 0w; 0w; 74w; 224w; 15w; 64w; 249w; 0w; 0w;
              64w; 185w; 32w; 0w; 0w; 74w; 224w; 63w; 0w; 185w; 224w; 51w;
              64w; 185w; 0w; 124w; 24w; 83w; 224w; 83w; 0w; 185w; 224w;
              55w; 64w; 185w; 0w; 124w; 16w; 83w; 0w; 28w; 0w; 18w; 224w;
              87w; 0w; 185w; 224w; 59w; 64w; 185w; 0w; 124w; 8w; 83w; 0w;
              28w; 0w; 18w; 224w; 91w; 0w; 185w; 224w; 47w; 64w; 185w; 0w;
              28w; 0w; 18w; 224w; 95w; 0w; 185w; 224w; 83w; 64w; 185w; 1w;
              244w; 126w; 211w; 0w; 0w; 0w; 144w; 0w; 64w; 57w; 145w; 32w;
              0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 99w; 0w; 185w; 224w;
              87w; 64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w; 176w; 0w;
              64w; 9w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w;
              103w; 0w; 185w; 224w; 91w; 64w; 185w; 1w; 244w; 126w; 211w;
              0w; 0w; 0w; 176w; 0w; 64w; 25w; 145w; 32w; 0w; 0w; 139w; 0w;
              0w; 64w; 185w; 224w; 107w; 0w; 185w; 224w; 95w; 64w; 185w;
              1w; 244w; 126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w; 41w; 145w;
              32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 111w; 0w; 185w;
              225w; 99w; 64w; 185w; 224w; 103w; 64w; 185w; 33w; 0w; 0w;
              74w; 224w; 107w; 64w; 185w; 33w; 0w; 0w; 74w; 224w; 111w;
              64w; 185w; 33w; 0w; 0w; 74w; 224w; 15w; 64w; 249w; 0w; 16w;
              0w; 145w; 0w; 0w; 64w; 185w; 32w; 0w; 0w; 74w; 224w; 67w; 0w;
              185w; 224w; 55w; 64w; 185w; 0w; 124w; 24w; 83w; 224w; 83w;
              0w; 185w; 224w; 59w; 64w; 185w; 0w; 124w; 16w; 83w; 0w; 28w;
              0w; 18w; 224w; 87w; 0w; 185w; 224w; 47w; 64w; 185w; 0w; 124w;
              8w; 83w; 0w; 28w; 0w; 18w; 224w; 91w; 0w; 185w; 224w; 51w;
              64w; 185w; 0w; 28w; 0w; 18w; 224w; 95w; 0w; 185w; 224w; 83w;
              64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w; 144w; 0w; 64w;
              57w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 99w;
              0w; 185w; 224w; 87w; 64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w;
              0w; 176w; 0w; 64w; 9w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w;
              185w; 224w; 103w; 0w; 185w; 224w; 91w; 64w; 185w; 1w; 244w;
              126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w; 25w; 145w; 32w; 0w;
              0w; 139w; 0w; 0w; 64w; 185w; 224w; 107w; 0w; 185w; 224w; 95w;
              64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w;
              41w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 111w;
              0w; 185w; 225w; 99w; 64w; 185w; 224w; 103w; 64w; 185w; 33w;
              0w; 0w; 74w; 224w; 107w; 64w; 185w; 33w; 0w; 0w; 74w; 224w;
              111w; 64w; 185w; 33w; 0w; 0w; 74w; 224w; 15w; 64w; 249w; 0w;
              32w; 0w; 145w; 0w; 0w; 64w; 185w; 32w; 0w; 0w; 74w; 224w;
              71w; 0w; 185w; 224w; 59w; 64w; 185w; 0w; 124w; 24w; 83w;
              224w; 83w; 0w; 185w; 224w; 47w; 64w; 185w; 0w; 124w; 16w;
              83w; 0w; 28w; 0w; 18w; 224w; 87w; 0w; 185w; 224w; 51w; 64w;
              185w; 0w; 124w; 8w; 83w; 0w; 28w; 0w; 18w; 224w; 91w; 0w;
              185w; 224w; 55w; 64w; 185w; 0w; 28w; 0w; 18w; 224w; 95w; 0w;
              185w; 224w; 83w; 64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w;
              144w; 0w; 64w; 57w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w;
              185w; 224w; 99w; 0w; 185w; 224w; 87w; 64w; 185w; 1w; 244w;
              126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w; 9w; 145w; 32w; 0w; 0w;
              139w; 0w; 0w; 64w; 185w; 224w; 103w; 0w; 185w; 224w; 91w;
              64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w;
              25w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 107w;
              0w; 185w; 224w; 95w; 64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w;
              0w; 176w; 0w; 64w; 41w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w;
              185w; 224w; 111w; 0w; 185w; 225w; 99w; 64w; 185w; 224w; 103w;
              64w; 185w; 33w; 0w; 0w; 74w; 224w; 107w; 64w; 185w; 33w; 0w;
              0w; 74w; 224w; 111w; 64w; 185w; 33w; 0w; 0w; 74w; 224w; 15w;
              64w; 249w; 0w; 48w; 0w; 145w; 0w; 0w; 64w; 185w; 32w; 0w; 0w;
              74w; 224w; 75w; 0w; 185w; 224w; 63w; 64w; 185w; 224w; 47w;
              0w; 185w; 224w; 67w; 64w; 185w; 224w; 51w; 0w; 185w; 224w;
              71w; 64w; 185w; 224w; 55w; 0w; 185w; 224w; 75w; 64w; 185w;
              224w; 59w; 0w; 185w; 224w; 15w; 64w; 249w; 0w; 64w; 0w; 145w;
              224w; 15w; 0w; 249w; 224w; 79w; 64w; 185w; 0w; 4w; 0w; 81w;
              224w; 79w; 0w; 185w; 224w; 79w; 64w; 185w; 31w; 0w; 0w; 113w;
              33w; 227w; 255w; 84w; 224w; 63w; 64w; 185w; 0w; 124w; 24w;
              83w; 224w; 83w; 0w; 185w; 224w; 67w; 64w; 185w; 0w; 124w;
              16w; 83w; 0w; 28w; 0w; 18w; 224w; 87w; 0w; 185w; 224w; 71w;
              64w; 185w; 0w; 124w; 8w; 83w; 0w; 28w; 0w; 18w; 224w; 91w;
              0w; 185w; 224w; 75w; 64w; 185w; 0w; 28w; 0w; 18w; 224w; 95w;
              0w; 185w; 224w; 83w; 64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w;
              0w; 176w; 0w; 64w; 25w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w;
              185w; 224w; 99w; 0w; 185w; 224w; 87w; 64w; 185w; 1w; 244w;
              126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w; 41w; 145w; 32w; 0w;
              0w; 139w; 0w; 0w; 64w; 185w; 224w; 103w; 0w; 185w; 224w; 91w;
              64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w; 144w; 0w; 64w;
              57w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 107w;
              0w; 185w; 224w; 95w; 64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w;
              0w; 176w; 0w; 64w; 9w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w;
              185w; 224w; 111w; 0w; 185w; 224w; 99w; 64w; 185w; 1w; 28w;
              8w; 18w; 224w; 103w; 64w; 185w; 0w; 28w; 16w; 18w; 33w; 0w;
              0w; 74w; 224w; 107w; 64w; 185w; 0w; 28w; 24w; 18w; 33w; 0w;
              0w; 74w; 224w; 111w; 64w; 185w; 0w; 28w; 0w; 18w; 33w; 0w;
              0w; 74w; 224w; 15w; 64w; 249w; 0w; 0w; 64w; 185w; 32w; 0w;
              0w; 74w; 224w; 47w; 0w; 185w; 224w; 67w; 64w; 185w; 0w; 124w;
              24w; 83w; 224w; 83w; 0w; 185w; 224w; 71w; 64w; 185w; 0w;
              124w; 16w; 83w; 0w; 28w; 0w; 18w; 224w; 87w; 0w; 185w; 224w;
              75w; 64w; 185w; 0w; 124w; 8w; 83w; 0w; 28w; 0w; 18w; 224w;
              91w; 0w; 185w; 224w; 63w; 64w; 185w; 0w; 28w; 0w; 18w; 224w;
              95w; 0w; 185w; 224w; 83w; 64w; 185w; 1w; 244w; 126w; 211w;
              0w; 0w; 0w; 176w; 0w; 64w; 25w; 145w; 32w; 0w; 0w; 139w; 0w;
              0w; 64w; 185w; 224w; 99w; 0w; 185w; 224w; 87w; 64w; 185w; 1w;
              244w; 126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w; 41w; 145w; 32w;
              0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 103w; 0w; 185w; 224w;
              91w; 64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w; 144w; 0w;
              64w; 57w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w;
              107w; 0w; 185w; 224w; 95w; 64w; 185w; 1w; 244w; 126w; 211w;
              0w; 0w; 0w; 176w; 0w; 64w; 9w; 145w; 32w; 0w; 0w; 139w; 0w;
              0w; 64w; 185w; 224w; 111w; 0w; 185w; 224w; 99w; 64w; 185w;
              1w; 28w; 8w; 18w; 224w; 103w; 64w; 185w; 0w; 28w; 16w; 18w;
              33w; 0w; 0w; 74w; 224w; 107w; 64w; 185w; 0w; 28w; 24w; 18w;
              33w; 0w; 0w; 74w; 224w; 111w; 64w; 185w; 0w; 28w; 0w; 18w;
              33w; 0w; 0w; 74w; 224w; 15w; 64w; 249w; 0w; 16w; 0w; 145w;
              0w; 0w; 64w; 185w; 32w; 0w; 0w; 74w; 224w; 51w; 0w; 185w;
              224w; 71w; 64w; 185w; 0w; 124w; 24w; 83w; 224w; 83w; 0w;
              185w; 224w; 75w; 64w; 185w; 0w; 124w; 16w; 83w; 0w; 28w; 0w;
              18w; 224w; 87w; 0w; 185w; 224w; 63w; 64w; 185w; 0w; 124w; 8w;
              83w; 0w; 28w; 0w; 18w; 224w; 91w; 0w; 185w; 224w; 67w; 64w;
              185w; 0w; 28w; 0w; 18w; 224w; 95w; 0w; 185w; 224w; 83w; 64w;
              185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w; 25w;
              145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 99w; 0w;
              185w; 224w; 87w; 64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w;
              176w; 0w; 64w; 41w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w;
              185w; 224w; 103w; 0w; 185w; 224w; 91w; 64w; 185w; 1w; 244w;
              126w; 211w; 0w; 0w; 0w; 144w; 0w; 64w; 57w; 145w; 32w; 0w;
              0w; 139w; 0w; 0w; 64w; 185w; 224w; 107w; 0w; 185w; 224w; 95w;
              64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w;
              9w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 111w;
              0w; 185w; 224w; 99w; 64w; 185w; 1w; 28w; 8w; 18w; 224w; 103w;
              64w; 185w; 0w; 28w; 16w; 18w; 33w; 0w; 0w; 74w; 224w; 107w;
              64w; 185w; 0w; 28w; 24w; 18w; 33w; 0w; 0w; 74w; 224w; 111w;
              64w; 185w; 0w; 28w; 0w; 18w; 33w; 0w; 0w; 74w; 224w; 15w;
              64w; 249w; 0w; 32w; 0w; 145w; 0w; 0w; 64w; 185w; 32w; 0w; 0w;
              74w; 224w; 55w; 0w; 185w; 224w; 75w; 64w; 185w; 0w; 124w;
              24w; 83w; 224w; 83w; 0w; 185w; 224w; 63w; 64w; 185w; 0w;
              124w; 16w; 83w; 0w; 28w; 0w; 18w; 224w; 87w; 0w; 185w; 224w;
              67w; 64w; 185w; 0w; 124w; 8w; 83w; 0w; 28w; 0w; 18w; 224w;
              91w; 0w; 185w; 224w; 71w; 64w; 185w; 0w; 28w; 0w; 18w; 224w;
              95w; 0w; 185w; 224w; 83w; 64w; 185w; 1w; 244w; 126w; 211w;
              0w; 0w; 0w; 176w; 0w; 64w; 25w; 145w; 32w; 0w; 0w; 139w; 0w;
              0w; 64w; 185w; 224w; 99w; 0w; 185w; 224w; 87w; 64w; 185w; 1w;
              244w; 126w; 211w; 0w; 0w; 0w; 176w; 0w; 64w; 41w; 145w; 32w;
              0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w; 103w; 0w; 185w; 224w;
              91w; 64w; 185w; 1w; 244w; 126w; 211w; 0w; 0w; 0w; 144w; 0w;
              64w; 57w; 145w; 32w; 0w; 0w; 139w; 0w; 0w; 64w; 185w; 224w;
              107w; 0w; 185w; 224w; 95w; 64w; 185w; 1w; 244w; 126w; 211w;
              0w; 0w; 0w; 176w; 0w; 64w; 9w; 145w; 32w; 0w; 0w; 139w; 0w;
              0w; 64w; 185w; 224w; 111w; 0w; 185w; 224w; 99w; 64w; 185w;
              1w; 28w; 8w; 18w; 224w; 103w; 64w; 185w; 0w; 28w; 16w; 18w;
              33w; 0w; 0w; 74w; 224w; 107w; 64w; 185w; 0w; 28w; 24w; 18w;
              33w; 0w; 0w; 74w; 224w; 111w; 64w; 185w; 0w; 28w; 0w; 18w;
              33w; 0w; 0w; 74w; 224w; 15w; 64w; 249w; 0w; 48w; 0w; 145w;
              0w; 0w; 64w; 185w; 32w; 0w; 0w; 74w; 224w; 59w; 0w; 185w;
              224w; 3w; 64w; 249w; 225w; 47w; 64w; 185w; 1w; 0w; 0w; 185w;
              224w; 3w; 64w; 249w; 0w; 16w; 0w; 145w; 225w; 51w; 64w; 185w;
              1w; 0w; 0w; 185w; 224w; 3w; 64w; 249w; 0w; 32w; 0w; 145w;
              225w; 55w; 64w; 185w; 1w; 0w; 0w; 185w; 224w; 3w; 64w; 249w;
              0w; 48w; 0w; 145w; 225w; 59w; 64w; 185w; 1w; 0w; 0w; 185w;
              31w; 32w; 3w; 213w; 255w; 195w; 1w; 145w; 192w; 3w; 95w;
              214w])]
           (BirProgram
              [<|bb_label :=
                   BL_Address_HC (Imm64 0x400570w)
                     "D101C3FF (sub sp, sp, #0x70)";
                 bb_statements :=
                   [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 112w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400574w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400574w)
                     "F9000FE0 (str x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) 8);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400578w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400578w)
                     "B90017E1 (str w1, [sp,#20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 20w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 20w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40057Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40057Cw)
                     "F90007E2 (str x2, [sp,#8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 8w))) 8);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R2" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400580w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400580w)
                     "F90003E3 (str x3, [sp])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))) 8);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400584w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400584w)
                     "B94017E0 (ldr w0, [sp,#20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 20w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400588w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400588w)
                     "51000400 (sub w0, w0, #0x1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Minus
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 1w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40058Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40058Cw)
                     "B9004FE0 (str w0, [sp,#76])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 76w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 76w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400590w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400590w)
                     "F94007E0 (ldr x0, [sp,#8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400594w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400594w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400598w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400598w)
                     "B9002FE0 (str w0, [sp,#44])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 44w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 44w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40059Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40059Cw)
                     "F94007E0 (ldr x0, [sp,#8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005A0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005A0w)
                     "B9400400 (ldr w0, [x0,#4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 4w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005A4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005A4w)
                     "B90033E0 (str w0, [sp,#48])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 48w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005A8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005A8w)
                     "F94007E0 (ldr x0, [sp,#8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005ACw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005ACw)
                     "B9400800 (ldr w0, [x0,#8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005B0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005B0w)
                     "B90037E0 (str w0, [sp,#52])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005B4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005B4w)
                     "F94007E0 (ldr x0, [sp,#8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005B8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005B8w)
                     "B9400C00 (ldr w0, [x0,#12])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 12w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005BCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005BCw)
                     "B9003BE0 (str w0, [sp,#56])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 56w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 56w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005C0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005C0w)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005C4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005C4w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005C8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005C8w)
                     "B9402FE1 (ldr w1, [sp,#44])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 44w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005CCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005CCw)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005D0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005D0w)
                     "B9002FE0 (str w0, [sp,#44])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 44w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 44w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005D4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005D4w)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005D8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005D8w)
                     "91001000 (add x0, x0, #0x4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005DCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005DCw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005E0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005E0w)
                     "B94033E1 (ldr w1, [sp,#48])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005E4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005E4w)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005E8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005E8w)
                     "B90033E0 (str w0, [sp,#48])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 48w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005ECw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005ECw)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005F0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005F0w)
                     "91002000 (add x0, x0, #0x8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 8w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005F4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005F4w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005F8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005F8w)
                     "B94037E1 (ldr w1, [sp,#52])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005FCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005FCw)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400600w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400600w)
                     "B90037E0 (str w0, [sp,#52])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400604w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400604w)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400608w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400608w)
                     "91003000 (add x0, x0, #0xc)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 12w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40060Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40060Cw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400610w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400610w)
                     "B9403BE1 (ldr w1, [sp,#56])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 56w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400614w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400614w)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400618w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400618w)
                     "B9003BE0 (str w0, [sp,#56])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 56w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 56w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40061Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40061Cw)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400620w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400620w)
                     "91004000 (add x0, x0, #0x10)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400624w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400624w)
                     "F9000FE0 (str x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) 8);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400628w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400628w) "140000E6 (b 0x4009c0)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009C0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40062Cw)
                     "B9402FE0 (ldr w0, [sp,#44])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 44w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400630w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400630w)
                     "53187C00 (lsr w0, w0, #24)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 24w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400634w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400634w)
                     "B90053E0 (str w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400638w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400638w)
                     "B94033E0 (ldr w0, [sp,#48])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40063Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40063Cw)
                     "53107C00 (lsr w0, w0, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 16w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400640w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400640w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400644w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400644w)
                     "B90057E0 (str w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400648w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400648w)
                     "B94037E0 (ldr w0, [sp,#52])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40064Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40064Cw)
                     "53087C00 (lsr w0, w0, #8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 8w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400650w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400650w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400654w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400654w)
                     "B9005BE0 (str w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400658w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400658w)
                     "B9403BE0 (ldr w0, [sp,#56])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 56w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40065Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40065Cw)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400660w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400660w)
                     "B9005FE0 (str w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400664w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400664w)
                     "B94053E0 (ldr w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400668w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400668w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40066Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40066Cw)
                     "90000000 (adrp x0, 0x400000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x400000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400670w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400670w)
                     "91394000 (add x0, x0, #0xe50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 3664w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400674w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400674w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400678w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400678w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40067Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40067Cw)
                     "B90063E0 (str w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400680w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400680w)
                     "B94057E0 (ldr w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400684w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400684w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400688w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400688w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40068Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40068Cw)
                     "91094000 (add x0, x0, #0x250)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 592w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400690w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400690w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400694w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400694w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400698w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400698w)
                     "B90067E0 (str w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40069Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40069Cw)
                     "B9405BE0 (ldr w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006A0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006A0w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006A4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006A4w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006A8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006A8w)
                     "91194000 (add x0, x0, #0x650)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 1616w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006ACw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006ACw)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006B0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006B0w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006B4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006B4w)
                     "B9006BE0 (str w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006B8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006B8w)
                     "B9405FE0 (ldr w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006BCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006BCw)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006C0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006C0w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006C4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006C4w)
                     "91294000 (add x0, x0, #0xa50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2640w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006C8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006C8w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006CCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006CCw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006D0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006D0w)
                     "B9006FE0 (str w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006D4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006D4w)
                     "B94063E1 (ldr w1, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006D8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006D8w)
                     "B94067E0 (ldr w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006DCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006DCw)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006E0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006E0w)
                     "B9406BE0 (ldr w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006E4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006E4w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006E8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006E8w)
                     "B9406FE0 (ldr w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006ECw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006ECw)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006F0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006F0w)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006F4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006F4w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006F8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006F8w)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4006FCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4006FCw)
                     "B9003FE0 (str w0, [sp,#60])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 60w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 60w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400700w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400700w)
                     "B94033E0 (ldr w0, [sp,#48])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400704w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400704w)
                     "53187C00 (lsr w0, w0, #24)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 24w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400708w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400708w)
                     "B90053E0 (str w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40070Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40070Cw)
                     "B94037E0 (ldr w0, [sp,#52])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400710w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400710w)
                     "53107C00 (lsr w0, w0, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 16w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400714w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400714w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400718w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400718w)
                     "B90057E0 (str w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40071Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40071Cw)
                     "B9403BE0 (ldr w0, [sp,#56])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 56w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400720w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400720w)
                     "53087C00 (lsr w0, w0, #8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 8w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400724w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400724w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400728w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400728w)
                     "B9005BE0 (str w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40072Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40072Cw)
                     "B9402FE0 (ldr w0, [sp,#44])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 44w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400730w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400730w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400734w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400734w)
                     "B9005FE0 (str w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400738w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400738w)
                     "B94053E0 (ldr w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40073Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40073Cw)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400740w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400740w)
                     "90000000 (adrp x0, 0x400000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x400000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400744w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400744w)
                     "91394000 (add x0, x0, #0xe50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 3664w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400748w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400748w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40074Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40074Cw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400750w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400750w)
                     "B90063E0 (str w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400754w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400754w)
                     "B94057E0 (ldr w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400758w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400758w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40075Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40075Cw)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400760w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400760w)
                     "91094000 (add x0, x0, #0x250)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 592w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400764w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400764w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400768w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400768w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40076Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40076Cw)
                     "B90067E0 (str w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400770w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400770w)
                     "B9405BE0 (ldr w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400774w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400774w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400778w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400778w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40077Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40077Cw)
                     "91194000 (add x0, x0, #0x650)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 1616w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400780w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400780w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400784w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400784w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400788w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400788w)
                     "B9006BE0 (str w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40078Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40078Cw)
                     "B9405FE0 (ldr w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400790w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400790w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400794w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400794w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400798w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400798w)
                     "91294000 (add x0, x0, #0xa50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2640w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40079Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40079Cw)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007A0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007A0w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007A4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007A4w)
                     "B9006FE0 (str w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007A8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007A8w)
                     "B94063E1 (ldr w1, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007ACw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007ACw)
                     "B94067E0 (ldr w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007B0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007B0w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007B4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007B4w)
                     "B9406BE0 (ldr w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007B8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007B8w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007BCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007BCw)
                     "B9406FE0 (ldr w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007C0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007C0w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007C4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007C4w)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007C8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007C8w)
                     "91001000 (add x0, x0, #0x4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007CCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007CCw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007D0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007D0w)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007D4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007D4w)
                     "B90043E0 (str w0, [sp,#64])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 64w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 64w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007D8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007D8w)
                     "B94037E0 (ldr w0, [sp,#52])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007DCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007DCw)
                     "53187C00 (lsr w0, w0, #24)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 24w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007E0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007E0w)
                     "B90053E0 (str w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007E4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007E4w)
                     "B9403BE0 (ldr w0, [sp,#56])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 56w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007E8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007E8w)
                     "53107C00 (lsr w0, w0, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 16w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007ECw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007ECw)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007F0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007F0w)
                     "B90057E0 (str w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007F4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007F4w)
                     "B9402FE0 (ldr w0, [sp,#44])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 44w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007F8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007F8w)
                     "53087C00 (lsr w0, w0, #8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 8w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4007FCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4007FCw)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400800w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400800w)
                     "B9005BE0 (str w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400804w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400804w)
                     "B94033E0 (ldr w0, [sp,#48])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400808w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400808w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40080Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40080Cw)
                     "B9005FE0 (str w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400810w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400810w)
                     "B94053E0 (ldr w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400814w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400814w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400818w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400818w)
                     "90000000 (adrp x0, 0x400000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x400000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40081Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40081Cw)
                     "91394000 (add x0, x0, #0xe50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 3664w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400820w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400820w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400824w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400824w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400828w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400828w)
                     "B90063E0 (str w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40082Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40082Cw)
                     "B94057E0 (ldr w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400830w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400830w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400834w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400834w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400838w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400838w)
                     "91094000 (add x0, x0, #0x250)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 592w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40083Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40083Cw)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400840w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400840w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400844w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400844w)
                     "B90067E0 (str w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400848w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400848w)
                     "B9405BE0 (ldr w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40084Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40084Cw)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400850w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400850w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400854w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400854w)
                     "91194000 (add x0, x0, #0x650)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 1616w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400858w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400858w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40085Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40085Cw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400860w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400860w)
                     "B9006BE0 (str w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400864w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400864w)
                     "B9405FE0 (ldr w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400868w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400868w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40086Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40086Cw)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400870w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400870w)
                     "91294000 (add x0, x0, #0xa50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2640w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400874w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400874w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400878w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400878w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40087Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40087Cw)
                     "B9006FE0 (str w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400880w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400880w)
                     "B94063E1 (ldr w1, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400884w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400884w)
                     "B94067E0 (ldr w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400888w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400888w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40088Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40088Cw)
                     "B9406BE0 (ldr w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400890w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400890w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400894w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400894w)
                     "B9406FE0 (ldr w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400898w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400898w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40089Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40089Cw)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008A0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008A0w)
                     "91002000 (add x0, x0, #0x8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 8w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008A4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008A4w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008A8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008A8w)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008ACw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008ACw)
                     "B90047E0 (str w0, [sp,#68])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 68w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 68w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008B0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008B0w)
                     "B9403BE0 (ldr w0, [sp,#56])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 56w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008B4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008B4w)
                     "53187C00 (lsr w0, w0, #24)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 24w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008B8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008B8w)
                     "B90053E0 (str w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008BCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008BCw)
                     "B9402FE0 (ldr w0, [sp,#44])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 44w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008C0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008C0w)
                     "53107C00 (lsr w0, w0, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 16w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008C4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008C4w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008C8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008C8w)
                     "B90057E0 (str w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008CCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008CCw)
                     "B94033E0 (ldr w0, [sp,#48])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008D0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008D0w)
                     "53087C00 (lsr w0, w0, #8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 8w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008D4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008D4w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008D8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008D8w)
                     "B9005BE0 (str w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008DCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008DCw)
                     "B94037E0 (ldr w0, [sp,#52])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008E0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008E0w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008E4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008E4w)
                     "B9005FE0 (str w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008E8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008E8w)
                     "B94053E0 (ldr w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008ECw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008ECw)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008F0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008F0w)
                     "90000000 (adrp x0, 0x400000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x400000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008F4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008F4w)
                     "91394000 (add x0, x0, #0xe50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 3664w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008F8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008F8w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4008FCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4008FCw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400900w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400900w)
                     "B90063E0 (str w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400904w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400904w)
                     "B94057E0 (ldr w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400908w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400908w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40090Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40090Cw)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400910w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400910w)
                     "91094000 (add x0, x0, #0x250)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 592w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400914w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400914w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400918w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400918w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40091Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40091Cw)
                     "B90067E0 (str w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400920w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400920w)
                     "B9405BE0 (ldr w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400924w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400924w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400928w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400928w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40092Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40092Cw)
                     "91194000 (add x0, x0, #0x650)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 1616w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400930w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400930w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400934w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400934w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400938w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400938w)
                     "B9006BE0 (str w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40093Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40093Cw)
                     "B9405FE0 (ldr w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400940w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400940w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400944w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400944w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400948w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400948w)
                     "91294000 (add x0, x0, #0xa50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2640w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40094Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40094Cw)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400950w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400950w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400954w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400954w)
                     "B9006FE0 (str w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400958w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400958w)
                     "B94063E1 (ldr w1, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40095Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40095Cw)
                     "B94067E0 (ldr w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400960w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400960w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400964w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400964w)
                     "B9406BE0 (ldr w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400968w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400968w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40096Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40096Cw)
                     "B9406FE0 (ldr w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400970w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400970w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400974w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400974w)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400978w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400978w)
                     "91003000 (add x0, x0, #0xc)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 12w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40097Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40097Cw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400980w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400980w)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400984w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400984w)
                     "B9004BE0 (str w0, [sp,#72])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 72w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 72w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400988w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400988w)
                     "B9403FE0 (ldr w0, [sp,#60])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 60w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40098Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40098Cw)
                     "B9002FE0 (str w0, [sp,#44])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 44w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 44w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400990w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400990w)
                     "B94043E0 (ldr w0, [sp,#64])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 64w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400994w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400994w)
                     "B90033E0 (str w0, [sp,#48])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 48w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400998w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400998w)
                     "B94047E0 (ldr w0, [sp,#68])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 68w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40099Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40099Cw)
                     "B90037E0 (str w0, [sp,#52])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009A0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009A0w)
                     "B9404BE0 (ldr w0, [sp,#72])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 72w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009A4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009A4w)
                     "B9003BE0 (str w0, [sp,#56])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 56w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 56w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009A8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009A8w)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009ACw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009ACw)
                     "91004000 (add x0, x0, #0x10)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009B0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009B0w)
                     "F9000FE0 (str x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) 8);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009B4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009B4w)
                     "B9404FE0 (ldr w0, [sp,#76])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 76w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009B8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009B8w)
                     "51000400 (sub w0, w0, #0x1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Minus
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 1w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009BCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009BCw)
                     "B9004FE0 (str w0, [sp,#76])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 76w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 76w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009C0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009C0w)
                     "B9404FE0 (ldr w0, [sp,#76])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 76w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009C4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009C4w)
                     "7100001F (cmp w0, #0x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "ProcState_C" BType_Bool)
                      bir_exp_true;
                    BStmt_Assign (BVar "ProcState_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32));
                    BStmt_Assign (BVar "ProcState_V" BType_Bool)
                      bir_exp_false;
                    BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                         (BExp_Const (Imm32 0w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009C8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009C8w)
                     "54FFE321 (b.ne 0x40062c)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm64 0x4009CCw)))
                     (BLE_Label (BL_Address (Imm64 0x40062Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009CCw)
                     "B9403FE0 (ldr w0, [sp,#60])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 60w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009D0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009D0w)
                     "53187C00 (lsr w0, w0, #24)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 24w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009D4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009D4w)
                     "B90053E0 (str w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009D8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009D8w)
                     "B94043E0 (ldr w0, [sp,#64])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 64w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009DCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009DCw)
                     "53107C00 (lsr w0, w0, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 16w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009E0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009E0w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009E4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009E4w)
                     "B90057E0 (str w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009E8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009E8w)
                     "B94047E0 (ldr w0, [sp,#68])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 68w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009ECw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009ECw)
                     "53087C00 (lsr w0, w0, #8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 8w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009F0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009F0w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009F4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009F4w)
                     "B9005BE0 (str w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009F8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009F8w)
                     "B9404BE0 (ldr w0, [sp,#72])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 72w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009FCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009FCw)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A00w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A00w)
                     "B9005FE0 (str w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A04w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A04w)
                     "B94053E0 (ldr w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A08w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A08w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A0Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A0Cw)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A10w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A10w)
                     "91194000 (add x0, x0, #0x650)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 1616w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A14w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A14w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A18w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A18w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A1Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A1Cw)
                     "B90063E0 (str w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A20w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A20w)
                     "B94057E0 (ldr w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A24w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A24w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A28w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A28w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A2Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A2Cw)
                     "91294000 (add x0, x0, #0xa50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2640w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A30w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A30w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A34w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A34w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A38w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A38w)
                     "B90067E0 (str w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A3Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A3Cw)
                     "B9405BE0 (ldr w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A40w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A40w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A44w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A44w)
                     "90000000 (adrp x0, 0x400000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x400000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A48w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A48w)
                     "91394000 (add x0, x0, #0xe50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 3664w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A4Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A4Cw)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A50w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A50w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A54w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A54w)
                     "B9006BE0 (str w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A58w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A58w)
                     "B9405FE0 (ldr w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A5Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A5Cw)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A60w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A60w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A64w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A64w)
                     "91094000 (add x0, x0, #0x250)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 592w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A68w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A68w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A6Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A6Cw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A70w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A70w)
                     "B9006FE0 (str w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A74w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A74w)
                     "B94063E0 (ldr w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A78w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A78w)
                     "12081C01 (and w1, w0, #0xff000000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And
                            (BExp_Const (Imm32 0xFF000000w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A7Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A7Cw)
                     "B94067E0 (ldr w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A80w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A80w)
                     "12101C00 (and w0, w0, #0xff0000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And
                            (BExp_Const (Imm32 0xFF0000w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A84w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A84w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A88w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A88w)
                     "B9406BE0 (ldr w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A8Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A8Cw)
                     "12181C00 (and w0, w0, #0xff00)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 65280w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A90w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A90w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A94w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A94w)
                     "B9406FE0 (ldr w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A98w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A98w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400A9Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400A9Cw)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AA0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AA0w)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AA4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AA4w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AA8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AA8w)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AACw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AACw)
                     "B9002FE0 (str w0, [sp,#44])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 44w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 44w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AB0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AB0w)
                     "B94043E0 (ldr w0, [sp,#64])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 64w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AB4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AB4w)
                     "53187C00 (lsr w0, w0, #24)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 24w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AB8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AB8w)
                     "B90053E0 (str w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400ABCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400ABCw)
                     "B94047E0 (ldr w0, [sp,#68])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 68w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AC0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AC0w)
                     "53107C00 (lsr w0, w0, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 16w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AC4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AC4w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AC8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AC8w)
                     "B90057E0 (str w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400ACCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400ACCw)
                     "B9404BE0 (ldr w0, [sp,#72])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 72w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AD0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AD0w)
                     "53087C00 (lsr w0, w0, #8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 8w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AD4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AD4w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AD8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AD8w)
                     "B9005BE0 (str w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400ADCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400ADCw)
                     "B9403FE0 (ldr w0, [sp,#60])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 60w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AE0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AE0w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AE4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AE4w)
                     "B9005FE0 (str w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AE8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AE8w)
                     "B94053E0 (ldr w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AECw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AECw)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AF0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AF0w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AF4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AF4w)
                     "91194000 (add x0, x0, #0x650)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 1616w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AF8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AF8w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400AFCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400AFCw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B00w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B00w)
                     "B90063E0 (str w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B04w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B04w)
                     "B94057E0 (ldr w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B08w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B08w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B0Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B0Cw)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B10w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B10w)
                     "91294000 (add x0, x0, #0xa50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2640w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B14w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B14w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B18w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B18w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B1Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B1Cw)
                     "B90067E0 (str w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B20w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B20w)
                     "B9405BE0 (ldr w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B24w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B24w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B28w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B28w)
                     "90000000 (adrp x0, 0x400000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x400000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B2Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B2Cw)
                     "91394000 (add x0, x0, #0xe50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 3664w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B30w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B30w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B34w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B34w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B38w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B38w)
                     "B9006BE0 (str w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B3Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B3Cw)
                     "B9405FE0 (ldr w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B40w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B40w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B44w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B44w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B48w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B48w)
                     "91094000 (add x0, x0, #0x250)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 592w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B4Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B4Cw)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B50w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B50w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B54w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B54w)
                     "B9006FE0 (str w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B58w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B58w)
                     "B94063E0 (ldr w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B5Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B5Cw)
                     "12081C01 (and w1, w0, #0xff000000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And
                            (BExp_Const (Imm32 0xFF000000w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B60w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B60w)
                     "B94067E0 (ldr w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B64w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B64w)
                     "12101C00 (and w0, w0, #0xff0000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And
                            (BExp_Const (Imm32 0xFF0000w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B68w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B68w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B6Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B6Cw)
                     "B9406BE0 (ldr w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B70w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B70w)
                     "12181C00 (and w0, w0, #0xff00)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 65280w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B74w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B74w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B78w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B78w)
                     "B9406FE0 (ldr w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B7Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B7Cw)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B80w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B80w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B84w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B84w)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B88w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B88w)
                     "91001000 (add x0, x0, #0x4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B8Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B8Cw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B90w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B90w)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B94w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B94w)
                     "B90033E0 (str w0, [sp,#48])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 48w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B98w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B98w)
                     "B94047E0 (ldr w0, [sp,#68])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 68w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400B9Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400B9Cw)
                     "53187C00 (lsr w0, w0, #24)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 24w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BA0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BA0w)
                     "B90053E0 (str w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BA4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BA4w)
                     "B9404BE0 (ldr w0, [sp,#72])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 72w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BA8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BA8w)
                     "53107C00 (lsr w0, w0, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 16w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BACw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BACw)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BB0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BB0w)
                     "B90057E0 (str w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BB4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BB4w)
                     "B9403FE0 (ldr w0, [sp,#60])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 60w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BB8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BB8w)
                     "53087C00 (lsr w0, w0, #8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 8w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BBCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BBCw)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BC0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BC0w)
                     "B9005BE0 (str w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BC4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BC4w)
                     "B94043E0 (ldr w0, [sp,#64])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 64w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BC8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BC8w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BCCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BCCw)
                     "B9005FE0 (str w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BD0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BD0w)
                     "B94053E0 (ldr w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BD4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BD4w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BD8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BD8w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BDCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BDCw)
                     "91194000 (add x0, x0, #0x650)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 1616w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BE0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BE0w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BE4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BE4w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BE8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BE8w)
                     "B90063E0 (str w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BECw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BECw)
                     "B94057E0 (ldr w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BF0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BF0w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BF4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BF4w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BF8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BF8w)
                     "91294000 (add x0, x0, #0xa50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2640w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400BFCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400BFCw)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C00w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C00w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C04w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C04w)
                     "B90067E0 (str w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C08w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C08w)
                     "B9405BE0 (ldr w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C0Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C0Cw)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C10w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C10w)
                     "90000000 (adrp x0, 0x400000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x400000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C14w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C14w)
                     "91394000 (add x0, x0, #0xe50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 3664w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C18w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C18w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C1Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C1Cw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C20w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C20w)
                     "B9006BE0 (str w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C24w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C24w)
                     "B9405FE0 (ldr w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C28w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C28w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C2Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C2Cw)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C30w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C30w)
                     "91094000 (add x0, x0, #0x250)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 592w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C34w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C34w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C38w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C38w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C3Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C3Cw)
                     "B9006FE0 (str w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C40w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C40w)
                     "B94063E0 (ldr w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C44w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C44w)
                     "12081C01 (and w1, w0, #0xff000000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And
                            (BExp_Const (Imm32 0xFF000000w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C48w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C48w)
                     "B94067E0 (ldr w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C4Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C4Cw)
                     "12101C00 (and w0, w0, #0xff0000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And
                            (BExp_Const (Imm32 0xFF0000w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C50w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C50w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C54w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C54w)
                     "B9406BE0 (ldr w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C58w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C58w)
                     "12181C00 (and w0, w0, #0xff00)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 65280w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C5Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C5Cw)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C60w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C60w)
                     "B9406FE0 (ldr w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C64w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C64w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C68w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C68w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C6Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C6Cw)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C70w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C70w)
                     "91002000 (add x0, x0, #0x8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 8w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C74w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C74w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C78w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C78w)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C7Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C7Cw)
                     "B90037E0 (str w0, [sp,#52])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C80w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C80w)
                     "B9404BE0 (ldr w0, [sp,#72])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 72w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C84w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C84w)
                     "53187C00 (lsr w0, w0, #24)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 24w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C88w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C88w)
                     "B90053E0 (str w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C8Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C8Cw)
                     "B9403FE0 (ldr w0, [sp,#60])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 60w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C90w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C90w)
                     "53107C00 (lsr w0, w0, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 16w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C94w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C94w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C98w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C98w)
                     "B90057E0 (str w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400C9Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400C9Cw)
                     "B94043E0 (ldr w0, [sp,#64])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 64w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CA0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CA0w)
                     "53087C00 (lsr w0, w0, #8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32) (BExp_Const (Imm32 8w))) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CA4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CA4w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CA8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CA8w)
                     "B9005BE0 (str w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CACw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CACw)
                     "B94047E0 (ldr w0, [sp,#68])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 68w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CB0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CB0w)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CB4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CB4w)
                     "B9005FE0 (str w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CB8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CB8w)
                     "B94053E0 (ldr w0, [sp,#80])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 80w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CBCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CBCw)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CC0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CC0w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CC4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CC4w)
                     "91194000 (add x0, x0, #0x650)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 1616w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CC8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CC8w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CCCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CCCw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CD0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CD0w)
                     "B90063E0 (str w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CD4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CD4w)
                     "B94057E0 (ldr w0, [sp,#84])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 84w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CD8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CD8w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CDCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CDCw)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CE0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CE0w)
                     "91294000 (add x0, x0, #0xa50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2640w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CE4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CE4w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CE8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CE8w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CECw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CECw)
                     "B90067E0 (str w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CF0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CF0w)
                     "B9405BE0 (ldr w0, [sp,#88])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 88w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CF4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CF4w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CF8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CF8w)
                     "90000000 (adrp x0, 0x400000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x400000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400CFCw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400CFCw)
                     "91394000 (add x0, x0, #0xe50)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 3664w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D00w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D00w)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D04w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D04w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D08w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D08w)
                     "B9006BE0 (str w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D0Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D0Cw)
                     "B9405FE0 (ldr w0, [sp,#92])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 92w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D10w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D10w)
                     "D37EF401 (lsl x1, x0, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D14w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D14w)
                     "B0000000 (adrp x0, 0x401000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Const (Imm64 0x401000w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D18w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D18w)
                     "91094000 (add x0, x0, #0x250)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 592w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D1Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D1Cw)
                     "8B000020 (add x0, x1, x0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D20w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D20w)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D24w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D24w)
                     "B9006FE0 (str w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D28w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D28w)
                     "B94063E0 (ldr w0, [sp,#96])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 96w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D2Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D2Cw)
                     "12081C01 (and w1, w0, #0xff000000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And
                            (BExp_Const (Imm32 0xFF000000w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D30w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D30w)
                     "B94067E0 (ldr w0, [sp,#100])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 100w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D34w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D34w)
                     "12101C00 (and w0, w0, #0xff0000)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And
                            (BExp_Const (Imm32 0xFF0000w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D38w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D38w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D3Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D3Cw)
                     "B9406BE0 (ldr w0, [sp,#104])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 104w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D40w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D40w)
                     "12181C00 (and w0, w0, #0xff00)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 65280w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D44w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D44w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D48w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D48w)
                     "B9406FE0 (ldr w0, [sp,#108])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 108w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D4Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D4Cw)
                     "12001C00 (and w0, w0, #0xff)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D50w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D50w)
                     "4A000021 (eor w1, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D54w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D54w)
                     "F9400FE0 (ldr x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D58w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D58w)
                     "91003000 (add x0, x0, #0xc)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 12w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D5Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D5Cw)
                     "B9400000 (ldr w0, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            BEnd_LittleEndian Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D60w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D60w)
                     "4A000020 (eor w0, w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Xor
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D64w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D64w)
                     "B9003BE0 (str w0, [sp,#56])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 56w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 56w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D68w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D68w)
                     "F94003E0 (ldr x0, [sp])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         BEnd_LittleEndian Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D6Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D6Cw)
                     "B9402FE1 (ldr w1, [sp,#44])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 44w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D70w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D70w)
                     "B9000001 (str w1, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D74w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D74w)
                     "F94003E0 (ldr x0, [sp])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         BEnd_LittleEndian Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D78w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D78w)
                     "91001000 (add x0, x0, #0x4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D7Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D7Cw)
                     "B94033E1 (ldr w1, [sp,#48])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D80w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D80w)
                     "B9000001 (str w1, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D84w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D84w)
                     "F94003E0 (ldr x0, [sp])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         BEnd_LittleEndian Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D88w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D88w)
                     "91002000 (add x0, x0, #0x8)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 8w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D8Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D8Cw)
                     "B94037E1 (ldr w1, [sp,#52])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 52w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D90w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D90w)
                     "B9000001 (str w1, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D94w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D94w)
                     "F94003E0 (ldr x0, [sp])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         BEnd_LittleEndian Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D98w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D98w)
                     "91003000 (add x0, x0, #0xc)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 12w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400D9Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400D9Cw)
                     "B9403BE1 (ldr w1, [sp,#56])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 56w))) BEnd_LittleEndian
                            Bit32) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400DA0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400DA0w)
                     "B9000001 (str w1, [x0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400DA4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400DA4w) "D503201F (nop)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400DA8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400DA8w)
                     "9101C3FF (add sp, sp, #0x70)";
                 bb_statements :=
                   [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 112w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400DACw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400DACw) "D65F03C0 (ret)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>])

   [aes_m0_program_THM]  Theorem

       []
      |- bir_is_lifted_prog (m0_bmr (F,T)) (WI_end 0w 0x10000w)
           [(0w,
             [27w; 75w; 247w; 181w; 4w; 203w; 16w; 0w; 25w; 0w; 16w; 48w;
              20w; 120w; 12w; 112w; 84w; 120w; 76w; 112w; 148w; 120w; 140w;
              112w; 212w; 120w; 4w; 50w; 204w; 112w; 4w; 49w; 130w; 66w;
              243w; 209w; 19w; 73w; 4w; 34w; 140w; 70w; 19w; 72w; 3w; 39w;
              25w; 123w; 94w; 123w; 157w; 123w; 220w; 123w; 58w; 66w; 9w;
              209w; 103w; 70w; 134w; 93w; 1w; 150w; 70w; 93w; 5w; 93w; 68w;
              92w; 145w; 8w; 121w; 92w; 1w; 159w; 121w; 64w; 31w; 120w; 1w;
              50w; 121w; 64w; 25w; 116w; 89w; 120w; 78w; 64w; 153w; 120w;
              94w; 116w; 77w; 64w; 217w; 120w; 157w; 116w; 76w; 64w; 220w;
              116w; 4w; 51w; 44w; 42w; 222w; 209w; 247w; 189w; 0w; 0w; 0w;
              0w; 0w; 0w; 0w; 1w; 0w; 0w; 0w; 0w; 247w; 181w; 0w; 34w; 11w;
              75w; 12w; 76w; 95w; 107w; 35w; 29w; 0w; 1w; 1w; 147w; 1w;
              155w; 17w; 24w; 89w; 24w; 0w; 35w; 190w; 24w; 245w; 92w;
              172w; 70w; 100w; 70w; 205w; 92w; 101w; 64w; 245w; 84w; 1w;
              51w; 4w; 43w; 246w; 209w; 4w; 50w; 16w; 42w; 238w; 209w;
              247w; 189w; 0w; 0w; 128w; 0w; 0w; 0w; 0w; 0w; 7w; 75w; 16w;
              181w; 91w; 107w; 7w; 72w; 25w; 29w; 0w; 34w; 156w; 92w; 4w;
              93w; 156w; 84w; 4w; 50w; 16w; 42w; 249w; 209w; 1w; 51w; 153w;
              66w; 245w; 209w; 16w; 189w; 0w; 0w; 128w; 0w; 0w; 0w; 0w; 0w;
              13w; 75w; 91w; 107w; 89w; 121w; 90w; 120w; 89w; 112w; 89w;
              122w; 89w; 113w; 89w; 123w; 90w; 115w; 89w; 114w; 153w; 122w;
              154w; 120w; 153w; 112w; 153w; 123w; 154w; 114w; 154w; 121w;
              153w; 113w; 217w; 123w; 154w; 115w; 218w; 120w; 217w; 112w;
              217w; 122w; 217w; 115w; 217w; 121w; 218w; 113w; 217w; 114w;
              112w; 71w; 192w; 70w; 0w; 0w; 128w; 0w; 27w; 35w; 194w; 9w;
              83w; 67w; 64w; 0w; 88w; 64w; 192w; 178w; 112w; 71w; 8w; 75w;
              16w; 181w; 91w; 107w; 7w; 73w; 24w; 29w; 11w; 49w; 0w; 34w;
              156w; 92w; 12w; 93w; 156w; 84w; 4w; 50w; 16w; 42w; 249w;
              209w; 1w; 51w; 152w; 66w; 245w; 209w; 16w; 189w; 0w; 0w;
              128w; 0w; 0w; 0w; 0w; 1w; 13w; 75w; 91w; 107w; 89w; 122w;
              90w; 123w; 89w; 115w; 89w; 121w; 89w; 114w; 89w; 120w; 90w;
              112w; 89w; 113w; 153w; 122w; 154w; 120w; 153w; 112w; 153w;
              123w; 154w; 114w; 154w; 121w; 153w; 113w; 217w; 121w; 154w;
              115w; 218w; 120w; 217w; 112w; 217w; 122w; 217w; 113w; 217w;
              123w; 218w; 115w; 217w; 114w; 112w; 71w; 192w; 70w; 0w; 0w;
              128w; 0w; 240w; 181w; 0w; 32w; 135w; 176w; 255w; 247w; 113w;
              255w; 1w; 37w; 255w; 247w; 140w; 255w; 255w; 247w; 158w;
              255w; 34w; 75w; 92w; 107w; 35w; 0w; 16w; 51w; 5w; 147w; 35w;
              120w; 103w; 120w; 1w; 147w; 24w; 0w; 163w; 120w; 120w; 64w;
              2w; 147w; 227w; 120w; 3w; 147w; 3w; 154w; 2w; 155w; 83w; 64w;
              30w; 0w; 4w; 147w; 70w; 64w; 255w; 247w; 166w; 255w; 1w;
              155w; 88w; 64w; 112w; 64w; 32w; 112w; 2w; 152w; 120w; 64w;
              255w; 247w; 158w; 255w; 71w; 64w; 119w; 64w; 103w; 112w; 4w;
              152w; 255w; 247w; 152w; 255w; 2w; 155w; 88w; 64w; 112w; 64w;
              160w; 112w; 3w; 155w; 1w; 152w; 88w; 64w; 255w; 247w; 143w;
              255w; 3w; 155w; 88w; 64w; 70w; 64w; 5w; 155w; 230w; 112w; 4w;
              52w; 156w; 66w; 207w; 209w; 40w; 0w; 1w; 53w; 237w; 178w;
              255w; 247w; 50w; 255w; 10w; 45w; 191w; 209w; 255w; 247w; 76w;
              255w; 255w; 247w; 94w; 255w; 40w; 0w; 255w; 247w; 41w; 255w;
              7w; 176w; 240w; 189w; 192w; 70w; 0w; 0w; 128w; 0w; 240w;
              181w; 10w; 32w; 143w; 176w; 255w; 247w; 31w; 255w; 9w; 36w;
              255w; 247w; 136w; 255w; 255w; 247w; 113w; 255w; 32w; 0w;
              255w; 247w; 23w; 255w; 72w; 75w; 93w; 107w; 43w; 0w; 16w;
              51w; 13w; 147w; 43w; 120w; 4w; 147w; 107w; 120w; 4w; 152w;
              5w; 147w; 171w; 120w; 0w; 147w; 235w; 120w; 1w; 147w; 255w;
              247w; 87w; 255w; 6w; 144w; 255w; 247w; 84w; 255w; 7w; 144w;
              255w; 247w; 81w; 255w; 2w; 144w; 5w; 152w; 255w; 247w; 77w;
              255w; 8w; 144w; 255w; 247w; 74w; 255w; 9w; 144w; 255w; 247w;
              71w; 255w; 3w; 144w; 0w; 152w; 255w; 247w; 67w; 255w; 10w;
              144w; 255w; 247w; 64w; 255w; 7w; 0w; 255w; 247w; 61w; 255w;
              6w; 0w; 1w; 152w; 255w; 247w; 57w; 255w; 11w; 144w; 255w;
              247w; 54w; 255w; 12w; 144w; 255w; 247w; 51w; 255w; 7w; 154w;
              6w; 155w; 83w; 64w; 2w; 154w; 83w; 64w; 8w; 154w; 83w; 64w;
              3w; 154w; 83w; 64w; 123w; 64w; 5w; 154w; 115w; 64w; 67w; 64w;
              83w; 64w; 0w; 154w; 83w; 64w; 1w; 154w; 83w; 64w; 43w; 112w;
              2w; 154w; 8w; 155w; 83w; 64w; 9w; 154w; 83w; 64w; 3w; 154w;
              2w; 153w; 83w; 64w; 10w; 154w; 83w; 64w; 12w; 154w; 115w;
              64w; 83w; 64w; 4w; 154w; 67w; 64w; 83w; 64w; 0w; 154w; 83w;
              64w; 1w; 154w; 83w; 64w; 107w; 112w; 4w; 154w; 5w; 155w; 83w;
              64w; 7w; 154w; 74w; 64w; 3w; 153w; 74w; 64w; 10w; 153w; 74w;
              64w; 87w; 64w; 11w; 154w; 119w; 64w; 87w; 64w; 1w; 154w; 71w;
              64w; 87w; 64w; 2w; 153w; 6w; 154w; 95w; 64w; 74w; 64w; 9w;
              153w; 175w; 112w; 74w; 64w; 3w; 153w; 74w; 64w; 11w; 153w;
              114w; 64w; 12w; 158w; 74w; 64w; 86w; 64w; 0w; 154w; 112w;
              64w; 80w; 64w; 88w; 64w; 13w; 155w; 232w; 112w; 4w; 53w;
              171w; 66w; 129w; 209w; 99w; 30w; 220w; 178w; 0w; 44w; 0w;
              208w; 112w; 231w; 255w; 247w; 249w; 254w; 255w; 247w; 226w;
              254w; 32w; 0w; 255w; 247w; 136w; 254w; 15w; 176w; 240w; 189w;
              0w; 0w; 128w; 0w; 5w; 75w; 16w; 181w; 156w; 107w; 0w; 35w;
              193w; 92w; 226w; 92w; 74w; 64w; 194w; 84w; 1w; 51w; 16w; 43w;
              248w; 209w; 16w; 189w; 0w; 0w; 128w; 0w; 112w; 181w; 20w; 0w;
              13w; 0w; 26w; 0w; 1w; 0w; 32w; 0w; 255w; 247w; 254w; 255w;
              4w; 75w; 92w; 99w; 4w; 75w; 29w; 96w; 255w; 247w; 42w; 254w;
              255w; 247w; 240w; 254w; 112w; 189w; 192w; 70w; 0w; 0w; 128w;
              0w; 0w; 0w; 0w; 0w; 112w; 181w; 20w; 0w; 13w; 0w; 26w; 0w;
              1w; 0w; 32w; 0w; 255w; 247w; 254w; 255w; 4w; 75w; 92w; 99w;
              4w; 75w; 29w; 96w; 255w; 247w; 20w; 254w; 255w; 247w; 44w;
              255w; 112w; 189w; 192w; 70w; 0w; 0w; 128w; 0w; 0w; 0w; 0w;
              0w; 247w; 181w; 1w; 146w; 15w; 34w; 13w; 0w; 1w; 153w; 6w;
              0w; 17w; 64w; 8w; 156w; 0w; 145w; 0w; 43w; 3w; 208w; 21w;
              74w; 19w; 96w; 255w; 247w; 253w; 253w; 0w; 44w; 1w; 208w;
              19w; 75w; 156w; 99w; 52w; 0w; 1w; 154w; 163w; 27w; 154w; 66w;
              15w; 217w; 40w; 0w; 255w; 247w; 171w; 255w; 41w; 0w; 16w;
              34w; 32w; 0w; 255w; 247w; 254w; 255w; 11w; 79w; 16w; 53w;
              124w; 99w; 255w; 247w; 175w; 254w; 188w; 99w; 16w; 52w; 235w;
              231w; 0w; 155w; 0w; 43w; 8w; 208w; 26w; 0w; 41w; 0w; 32w; 0w;
              255w; 247w; 254w; 255w; 3w; 75w; 92w; 99w; 255w; 247w; 160w;
              254w; 247w; 189w; 192w; 70w; 0w; 0w; 0w; 0w; 0w; 0w; 128w;
              0w; 247w; 181w; 1w; 146w; 15w; 34w; 13w; 0w; 1w; 153w; 6w;
              0w; 17w; 64w; 8w; 156w; 0w; 145w; 0w; 43w; 3w; 208w; 21w;
              74w; 19w; 96w; 255w; 247w; 195w; 253w; 0w; 44w; 1w; 208w;
              19w; 75w; 156w; 99w; 52w; 0w; 1w; 154w; 163w; 27w; 154w; 66w;
              15w; 217w; 41w; 0w; 16w; 34w; 32w; 0w; 255w; 247w; 254w;
              255w; 13w; 79w; 124w; 99w; 255w; 247w; 203w; 254w; 32w; 0w;
              255w; 247w; 104w; 255w; 16w; 52w; 189w; 99w; 16w; 53w; 235w;
              231w; 0w; 155w; 0w; 43w; 8w; 208w; 26w; 0w; 41w; 0w; 32w; 0w;
              255w; 247w; 254w; 255w; 3w; 75w; 92w; 99w; 255w; 247w; 184w;
              254w; 247w; 189w; 192w; 70w; 0w; 0w; 0w; 0w; 0w; 0w; 128w;
              0w])]
           (BirProgram
              [<|bb_label :=
                   BL_Address_HC (Imm32 0w)
                     "4B1B (ldr r3, [pc, #108] ; (70 <KeyExpansion+0x70>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 112w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 2w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 2w)
                     "B5F7 (push {r0, r1, r2, r4, r5, r6, r7, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 32w))) 32);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 32w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Store
                               (BExp_Store
                                  (BExp_Store
                                     (BExp_Store
                                        (BExp_Store
                                           (BExp_Store
                                              (BExp_Den
                                                 (BVar "MEM"
                                                    (BType_Mem Bit32
                                                       Bit8)))
                                              (BExp_BinExp BIExp_Minus
                                                 (BExp_Den
                                                    (BVar "SP_process"
                                                       (BType_Imm Bit32)))
                                                 (BExp_Const (Imm32 32w)))
                                              BEnd_LittleEndian
                                              (BExp_Den
                                                 (BVar "R0"
                                                    (BType_Imm Bit32))))
                                           (BExp_BinExp BIExp_Minus
                                              (BExp_Den
                                                 (BVar "SP_process"
                                                    (BType_Imm Bit32)))
                                              (BExp_Const (Imm32 28w)))
                                           BEnd_LittleEndian
                                           (BExp_Den
                                              (BVar "R1"
                                                 (BType_Imm Bit32))))
                                        (BExp_BinExp BIExp_Minus
                                           (BExp_Den
                                              (BVar "SP_process"
                                                 (BType_Imm Bit32)))
                                           (BExp_Const (Imm32 24w)))
                                        BEnd_LittleEndian
                                        (BExp_Den
                                           (BVar "R2" (BType_Imm Bit32))))
                                     (BExp_BinExp BIExp_Minus
                                        (BExp_Den
                                           (BVar "SP_process"
                                              (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 20w)))
                                     BEnd_LittleEndian
                                     (BExp_Den
                                        (BVar "R4" (BType_Imm Bit32))))
                                  (BExp_BinExp BIExp_Minus
                                     (BExp_Den
                                        (BVar "SP_process"
                                           (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 16w)))
                                  BEnd_LittleEndian
                                  (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                               (BExp_BinExp BIExp_Minus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 12w)))
                               BEnd_LittleEndian
                               (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 4w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 4w) "CB04 (ldmia r3!, {r2})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 6w)))|>;
               <|bb_label := BL_Address_HC (Imm32 6w) "0010 (movs r0, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R2" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 8w)))|>;
               <|bb_label := BL_Address_HC (Imm32 8w) "0019 (movs r1, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Den (BVar "R3" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 10w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 10w) "3010 (adds r0, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 12w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 12w) "7814 (ldrb r4, [r2, #0])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 14w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 14w) "700C (strb r4, [r1, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 16w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 16w) "7854 (ldrb r4, [r2, #1])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 18w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 18w) "704C (strb r4, [r1, #1])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 20w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 20w) "7894 (ldrb r4, [r2, #2])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 22w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 22w) "708C (strb r4, [r1, #2])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 24w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 24w) "78D4 (ldrb r4, [r2, #3])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 26w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 26w) "3204 (adds r2, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 28w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 28w) "70CC (strb r4, [r1, #3])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 30w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 30w) "3104 (adds r1, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 32w)))|>;
               <|bb_label := BL_Address_HC (Imm32 32w) "4282 (cmp r2, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 34w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 34w)
                     "D1F3 (bne.n c <KeyExpansion+0xc>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 36w)))
                     (BLE_Label (BL_Address (Imm32 12w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 36w)
                     "4913 (ldr r1, [pc, #76] ; (74 <KeyExpansion+0x74>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 116w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 38w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 38w) "2204 (movs r2, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Const (Imm32 4w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 40w)))|>;
               <|bb_label := BL_Address_HC (Imm32 40w) "468C (mov ip, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R12" (BType_Imm Bit32))
                      (BExp_Den (BVar "R1" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 42w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 42w)
                     "4813 (ldr r0, [pc, #76] ; (78 <KeyExpansion+0x78>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 120w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 44w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 44w) "2703 (movs r7, #3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Const (Imm32 3w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 46w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 46w) "7B19 (ldrb r1, [r3, #12])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 48w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 48w) "7B5E (ldrb r6, [r3, #13])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 13w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 50w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 50w) "7B9D (ldrb r5, [r3, #14])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 14w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 52w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 52w) "7BDC (ldrb r4, [r3, #15])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 15w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 54w)))|>;
               <|bb_label := BL_Address_HC (Imm32 54w) "423A (tst r2, r7)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 56w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 56w)
                     "D109 (bne.n 4e <KeyExpansion+0x4e>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 58w)))
                     (BLE_Label (BL_Address (Imm32 78w)))|>;
               <|bb_label := BL_Address_HC (Imm32 58w) "4667 (mov r7, ip)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Den (BVar "R12" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 60w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 60w) "5D86 (ldrb r6, [r0, r6])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 62w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 62w) "9601 (str r6, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 64w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 64w) "5D46 (ldrb r6, [r0, r5])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 66w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 66w) "5D05 (ldrb r5, [r0, r4])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 68w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 68w) "5C44 (ldrb r4, [r0, r1])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R1" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 70w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 70w) "0891 (lsrs r1, r2, #2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_word_bit Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))) 1);
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_RightShift
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 2w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 72w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 72w) "5C79 (ldrb r1, [r7, r1])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 74w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 74w) "9F01 (ldr r7, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 76w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 76w) "4079 (eors r1, r7)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 78w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 78w) "781F (ldrb r7, [r3, #0])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 80w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 80w) "3201 (adds r2, #1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 82w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 82w) "4079 (eors r1, r7)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 84w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 84w) "7419 (strb r1, [r3, #16])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 86w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 86w) "7859 (ldrb r1, [r3, #1])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 88w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 88w) "404E (eors r6, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 90w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 90w) "7899 (ldrb r1, [r3, #2])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 92w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 92w) "745E (strb r6, [r3, #17])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 17w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 17w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 94w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 94w) "404D (eors r5, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 96w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 96w) "78D9 (ldrb r1, [r3, #3])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 98w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 98w) "749D (strb r5, [r3, #18])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 18w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 18w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 100w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 100w) "404C (eors r4, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 102w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 102w) "74DC (strb r4, [r3, #19])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 19w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 19w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 104w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 104w) "3304 (adds r3, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 106w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 106w) "2A2C (cmp r2, #44 ; 0x2c)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 44w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 44w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 44w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 44w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 108w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 108w)
                     "D1DE (bne.n 2c <KeyExpansion+0x2c>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 110w)))
                     (BLE_Label (BL_Address (Imm32 44w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 110w)
                     "BDF7 (pop {r0, r1, r2, r4, r5, r6, r7, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 28w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 28w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 24w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 32w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 124w)
                     "B5F7 (push {r0, r1, r2, r4, r5, r6, r7, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 32w))) 32);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 32w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Store
                               (BExp_Store
                                  (BExp_Store
                                     (BExp_Store
                                        (BExp_Store
                                           (BExp_Store
                                              (BExp_Den
                                                 (BVar "MEM"
                                                    (BType_Mem Bit32
                                                       Bit8)))
                                              (BExp_BinExp BIExp_Minus
                                                 (BExp_Den
                                                    (BVar "SP_process"
                                                       (BType_Imm Bit32)))
                                                 (BExp_Const (Imm32 32w)))
                                              BEnd_LittleEndian
                                              (BExp_Den
                                                 (BVar "R0"
                                                    (BType_Imm Bit32))))
                                           (BExp_BinExp BIExp_Minus
                                              (BExp_Den
                                                 (BVar "SP_process"
                                                    (BType_Imm Bit32)))
                                              (BExp_Const (Imm32 28w)))
                                           BEnd_LittleEndian
                                           (BExp_Den
                                              (BVar "R1"
                                                 (BType_Imm Bit32))))
                                        (BExp_BinExp BIExp_Minus
                                           (BExp_Den
                                              (BVar "SP_process"
                                                 (BType_Imm Bit32)))
                                           (BExp_Const (Imm32 24w)))
                                        BEnd_LittleEndian
                                        (BExp_Den
                                           (BVar "R2" (BType_Imm Bit32))))
                                     (BExp_BinExp BIExp_Minus
                                        (BExp_Den
                                           (BVar "SP_process"
                                              (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 20w)))
                                     BEnd_LittleEndian
                                     (BExp_Den
                                        (BVar "R4" (BType_Imm Bit32))))
                                  (BExp_BinExp BIExp_Minus
                                     (BExp_Den
                                        (BVar "SP_process"
                                           (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 16w)))
                                  BEnd_LittleEndian
                                  (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                               (BExp_BinExp BIExp_Minus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 12w)))
                               BEnd_LittleEndian
                               (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 126w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 126w) "2200 (movs r2, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Const (Imm32 0w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 128w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 128w)
                     "4B0B (ldr r3, [pc, #44] ; (b0 <AddRoundKey+0x34>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 176w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 130w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 130w)
                     "4C0C (ldr r4, [pc, #48] ; (b4 <AddRoundKey+0x38>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 180w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 132w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 132w)
                     "6B5F (ldr r7, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 134w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 134w) "1D23 (adds r3, r4, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 136w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 136w) "0100 (lsls r0, r0, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_word_bit Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))) 28);
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_word_bit Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))) 27);
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_LeftShift
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 138w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 138w) "9301 (str r3, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 140w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 140w) "9B01 (ldr r3, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 142w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 142w) "1811 (adds r1, r2, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 144w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 144w) "1859 (adds r1, r3, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 146w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 146w) "2300 (movs r3, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Const (Imm32 0w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 148w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 148w) "18BE (adds r6, r7, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 150w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 150w) "5CF5 (ldrb r5, [r6, r3])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 152w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 152w) "46AC (mov ip, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R12" (BType_Imm Bit32))
                      (BExp_Den (BVar "R5" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 154w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 154w) "4664 (mov r4, ip)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Den (BVar "R12" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 156w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 156w) "5CCD (ldrb r5, [r1, r3])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 158w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 158w) "4065 (eors r5, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 160w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 160w) "54F5 (strb r5, [r6, r3])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 162w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 162w) "3301 (adds r3, #1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 164w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 164w) "2B04 (cmp r3, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 166w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 166w)
                     "D1F6 (bne.n 96 <AddRoundKey+0x1a>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 168w)))
                     (BLE_Label (BL_Address (Imm32 150w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 168w) "3204 (adds r2, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 170w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 170w) "2A10 (cmp r2, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 172w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 172w)
                     "D1EE (bne.n 8c <AddRoundKey+0x10>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 174w)))
                     (BLE_Label (BL_Address (Imm32 140w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 174w)
                     "BDF7 (pop {r0, r1, r2, r4, r5, r6, r7, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 28w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 28w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 24w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 32w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 184w)
                     "4B07 (ldr r3, [pc, #28] ; (d8 <SubBytes+0x20>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 216w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 186w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 186w) "B510 (push {r4, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) 8);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 8w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 188w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 188w)
                     "6B5B (ldr r3, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 190w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 190w)
                     "4807 (ldr r0, [pc, #28] ; (dc <SubBytes+0x24>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 220w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 192w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 192w) "1D19 (adds r1, r3, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 194w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 194w) "2200 (movs r2, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Const (Imm32 0w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 196w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 196w) "5C9C (ldrb r4, [r3, r2])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 198w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 198w) "5D04 (ldrb r4, [r0, r4])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 200w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 200w) "549C (strb r4, [r3, r2])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 202w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 202w) "3204 (adds r2, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 204w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 204w) "2A10 (cmp r2, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 206w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 206w)
                     "D1F9 (bne.n c4 <SubBytes+0xc>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 208w)))
                     (BLE_Label (BL_Address (Imm32 196w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 208w) "3301 (adds r3, #1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 210w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 210w) "4299 (cmp r1, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 212w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 212w)
                     "D1F5 (bne.n c2 <SubBytes+0xa>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 214w)))
                     (BLE_Label (BL_Address (Imm32 194w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 214w) "BD10 (pop {r4, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 4w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 8w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 224w)
                     "4B0D (ldr r3, [pc, #52] ; (118 <ShiftRows+0x38>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 280w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 226w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 226w)
                     "6B5B (ldr r3, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 228w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 228w) "7959 (ldrb r1, [r3, #5])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 5w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 230w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 230w) "785A (ldrb r2, [r3, #1])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 232w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 232w) "7059 (strb r1, [r3, #1])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 234w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 234w) "7A59 (ldrb r1, [r3, #9])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 9w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 236w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 236w) "7159 (strb r1, [r3, #5])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 5w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 5w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 238w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 238w) "7B59 (ldrb r1, [r3, #13])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 13w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 240w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 240w) "735A (strb r2, [r3, #13])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 13w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 13w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 242w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 242w) "7259 (strb r1, [r3, #9])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 9w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 9w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 244w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 244w) "7A99 (ldrb r1, [r3, #10])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 10w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 246w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 246w) "789A (ldrb r2, [r3, #2])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 248w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 248w) "7099 (strb r1, [r3, #2])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 250w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 250w) "7B99 (ldrb r1, [r3, #14])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 14w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 252w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 252w) "729A (strb r2, [r3, #10])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 10w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 10w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 254w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 254w) "799A (ldrb r2, [r3, #6])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 6w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 256w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 256w) "7199 (strb r1, [r3, #6])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 6w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 6w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 258w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 258w) "7BD9 (ldrb r1, [r3, #15])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 15w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 260w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 260w) "739A (strb r2, [r3, #14])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 14w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 14w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 262w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 262w) "78DA (ldrb r2, [r3, #3])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 264w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 264w) "70D9 (strb r1, [r3, #3])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 266w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 266w) "7AD9 (ldrb r1, [r3, #11])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 11w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 268w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 268w) "73D9 (strb r1, [r3, #15])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 15w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 15w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 270w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 270w) "79D9 (ldrb r1, [r3, #7])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 7w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 272w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 272w) "71DA (strb r2, [r3, #7])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 7w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 7w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 274w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 274w) "72D9 (strb r1, [r3, #11])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 11w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 11w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 276w)))|>;
               <|bb_label := BL_Address_HC (Imm32 276w) "4770 (bx lr)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_LSB (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Align Bit32 1
                           (BExp_Den (BVar "LR" (BType_Imm Bit32)))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 278w)
                     "46C0 (nop   ; (mov r8, r8))"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 280w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 284w) "231B (movs r3, #27)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Const (Imm32 27w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 286w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 286w) "09C2 (lsrs r2, r0, #7)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_word_bit Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))) 6);
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 7w))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_RightShift
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 7w)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_RightShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 7w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 288w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 288w) "4353 (muls r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Mult
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Mult
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Mult
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 290w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 290w) "0040 (lsls r0, r0, #1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_word_bit Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))) 30);
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_LeftShift
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 292w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 292w) "4058 (eors r0, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 294w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 294w) "B2C0 (uxtb r0, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit32))) Bit8)
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 296w)))|>;
               <|bb_label := BL_Address_HC (Imm32 296w) "4770 (bx lr)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_LSB (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Align Bit32 1
                           (BExp_Den (BVar "LR" (BType_Imm Bit32)))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 298w)
                     "4B08 (ldr r3, [pc, #32] ; (14c <InvSubBytes+0x22>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 332w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 300w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 300w) "B510 (push {r4, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) 8);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 8w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 302w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 302w)
                     "6B5B (ldr r3, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 304w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 304w)
                     "4907 (ldr r1, [pc, #28] ; (150 <InvSubBytes+0x26>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 336w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 306w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 306w) "1D18 (adds r0, r3, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 308w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 308w) "310B (adds r1, #11)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 11w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 11w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 11w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 11w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 11w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 310w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 310w) "2200 (movs r2, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Const (Imm32 0w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 312w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 312w) "5C9C (ldrb r4, [r3, r2])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 314w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 314w) "5D0C (ldrb r4, [r1, r4])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 316w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 316w) "549C (strb r4, [r3, r2])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 318w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 318w) "3204 (adds r2, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 320w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 320w) "2A10 (cmp r2, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 322w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 322w)
                     "D1F9 (bne.n c4 <SubBytes+0xc>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 324w)))
                     (BLE_Label (BL_Address (Imm32 312w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 324w) "3301 (adds r3, #1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 326w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 326w) "4298 (cmp r0, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 328w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 328w)
                     "D1F5 (bne.n c2 <SubBytes+0xa>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 330w)))
                     (BLE_Label (BL_Address (Imm32 310w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 330w) "BD10 (pop {r4, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 4w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 8w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 340w)
                     "4B0D (ldr r3, [pc, #52] ; (118 <ShiftRows+0x38>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 396w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 342w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 342w)
                     "6B5B (ldr r3, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 344w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 344w) "7A59 (ldrb r1, [r3, #9])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 9w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 346w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 346w) "7B5A (ldrb r2, [r3, #13])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 13w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 348w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 348w) "7359 (strb r1, [r3, #13])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 13w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 13w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 350w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 350w) "7959 (ldrb r1, [r3, #5])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 5w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 352w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 352w) "7259 (strb r1, [r3, #9])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 9w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 9w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 354w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 354w) "7859 (ldrb r1, [r3, #1])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 356w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 356w) "705A (strb r2, [r3, #1])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 358w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 358w) "7159 (strb r1, [r3, #5])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 5w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 5w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 360w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 360w) "7A99 (ldrb r1, [r3, #10])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 10w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 362w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 362w) "789A (ldrb r2, [r3, #2])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 364w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 364w) "7099 (strb r1, [r3, #2])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 366w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 366w) "7B99 (ldrb r1, [r3, #14])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 14w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 368w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 368w) "729A (strb r2, [r3, #10])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 10w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 10w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 370w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 370w) "799A (ldrb r2, [r3, #6])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 6w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 372w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 372w) "7199 (strb r1, [r3, #6])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 6w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 6w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 374w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 374w) "79D9 (ldrb r1, [r3, #7])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 7w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 376w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 376w) "739A (strb r2, [r3, #14])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 14w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 14w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 378w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 378w) "78DA (ldrb r2, [r3, #3])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 380w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 380w) "70D9 (strb r1, [r3, #3])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 382w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 382w) "7AD9 (ldrb r1, [r3, #11])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 11w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 384w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 384w) "71D9 (strb r1, [r3, #7])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 7w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 7w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 386w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 386w) "7BD9 (ldrb r1, [r3, #15])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 15w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 388w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 388w) "73DA (strb r2, [r3, #15])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 15w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 15w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 390w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 390w) "72D9 (strb r1, [r3, #11])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 11w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 11w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 392w)))|>;
               <|bb_label := BL_Address_HC (Imm32 392w) "4770 (bx lr)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_LSB (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Align Bit32 1
                           (BExp_Den (BVar "LR" (BType_Imm Bit32)))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 394w)
                     "46C0 (nop   ; (mov r8, r8))"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 396w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 400w)
                     "B5F0 (push {r4, r5, r6, r7, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) 20);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 20w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Store
                               (BExp_Store
                                  (BExp_Store
                                     (BExp_Den
                                        (BVar "MEM"
                                           (BType_Mem Bit32 Bit8)))
                                     (BExp_BinExp BIExp_Minus
                                        (BExp_Den
                                           (BVar "SP_process"
                                              (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 20w)))
                                     BEnd_LittleEndian
                                     (BExp_Den
                                        (BVar "R4" (BType_Imm Bit32))))
                                  (BExp_BinExp BIExp_Minus
                                     (BExp_Den
                                        (BVar "SP_process"
                                           (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 16w)))
                                  BEnd_LittleEndian
                                  (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                               (BExp_BinExp BIExp_Minus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 12w)))
                               BEnd_LittleEndian
                               (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 402w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 402w) "2000 (movs r0, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Const (Imm32 0w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 404w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 404w) "B087 (sub sp, #28)";
                 bb_statements :=
                   [BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Align Bit32 2
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 28w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 406w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 406w)
                     "F7FFFF71 (bl 7c <AddRoundKey>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 411w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 124w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 410w) "2501 (movs r5, #1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 412w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 412w)
                     "F7FFFF8C (bl b8 <SubBytes>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 417w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 184w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 416w)
                     "F7FFFF9E (bl e0 <ShiftRows>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 421w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 224w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 420w)
                     "4B22 (ldr r3, [pc, #136] ; (230 <Cipher+0xa0>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 560w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 422w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 422w)
                     "6B5C (ldr r4, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 424w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 424w) "0023 (movs r3, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 426w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 426w) "3310 (adds r3, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 428w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 428w) "9305 (str r3, [sp, #20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 430w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 430w) "7823 (ldrb r3, [r4, #0])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 432w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 432w) "7867 (ldrb r7, [r4, #1])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 434w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 434w) "9301 (str r3, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 436w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 436w) "0018 (movs r0, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R3" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 438w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 438w) "78A3 (ldrb r3, [r4, #2])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 440w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 440w) "4078 (eors r0, r7)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 442w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 442w) "9302 (str r3, [sp, #8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 444w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 444w) "78E3 (ldrb r3, [r4, #3])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 446w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 446w) "9303 (str r3, [sp, #12])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 448w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 448w) "9A03 (ldr r2, [sp, #12])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 450w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 450w) "9B02 (ldr r3, [sp, #8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 452w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 452w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 454w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 454w) "001E (movs r6, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Den (BVar "R3" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 456w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 456w) "9304 (str r3, [sp, #16])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 458w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 458w) "4046 (eors r6, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 460w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 460w) "F7FFFFA6 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 465w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 464w) "9B01 (ldr r3, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 466w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 466w) "4058 (eors r0, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 468w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 468w) "4070 (eors r0, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 470w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 470w) "7020 (strb r0, [r4, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 472w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 472w) "9802 (ldr r0, [sp, #8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 474w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 474w) "4078 (eors r0, r7)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 476w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 476w)
                     "F7FFFF9E (bl e0 <ShiftRows>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 481w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 480w) "4047 (eors r7, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 482w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 482w) "4077 (eors r7, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R6" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 484w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 484w) "7067 (strb r7, [r4, #1])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 486w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 486w) "9804 (ldr r0, [sp, #16])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 488w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 488w) "F7FFFF98 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 493w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 492w) "9B02 (ldr r3, [sp, #8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 494w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 494w) "4058 (eors r0, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 496w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 496w) "4070 (eors r0, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 498w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 498w) "70A0 (strb r0, [r4, #2])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 500w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 500w) "9B03 (ldr r3, [sp, #12])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 502w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 502w) "9801 (ldr r0, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 504w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 504w) "4058 (eors r0, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 506w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 506w) "F7FFFF8F (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 511w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 510w) "9B03 (ldr r3, [sp, #12])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 512w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 512w) "4058 (eors r0, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 514w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 514w) "4046 (eors r6, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 516w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 516w) "9B05 (ldr r3, [sp, #20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 518w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 518w) "70E6 (strb r6, [r4, #3])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 520w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 520w) "3404 (adds r4, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 522w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 522w) "429C (cmp r4, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 524w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 524w)
                     "D1CF (bne.n 1ae <Cipher+0x1e>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 526w)))
                     (BLE_Label (BL_Address (Imm32 430w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 526w) "0028 (movs r0, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R5" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 528w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 528w) "3501 (adds r5, #1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 530w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 530w) "B2ED (uxtb r5, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R5" (BType_Imm Bit32))) Bit8)
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 532w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 532w)
                     "F7FFFF32 (bl 7c <AddRoundKey>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 537w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 124w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 536w) "2D0A (cmp r5, #10)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 10w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 10w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 10w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 10w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 538w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 538w)
                     "D1BF (bne.n 19c <Cipher+0xc>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 540w)))
                     (BLE_Label (BL_Address (Imm32 412w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 540w)
                     "F7FFFF4C (bl b8 <SubBytes>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 545w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 184w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 544w)
                     "F7FFFF5E (bl e0 <ShiftRows>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 549w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 224w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 548w) "0028 (movs r0, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R5" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 550w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 550w)
                     "F7FFFF29 (bl 7c <AddRoundKey>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 555w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 124w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 554w) "B007 (add sp, #28)";
                 bb_statements :=
                   [BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Align Bit32 2
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 28w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 556w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 556w)
                     "BDF0 (pop {r4, r5, r6, r7, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 16w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 20w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 558w)
                     "46C0 (nop   ; (mov r8, r8))"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 560w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 564w)
                     "B5F0 (push {r4, r5, r6, r7, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) 20);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 20w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Store
                               (BExp_Store
                                  (BExp_Store
                                     (BExp_Den
                                        (BVar "MEM"
                                           (BType_Mem Bit32 Bit8)))
                                     (BExp_BinExp BIExp_Minus
                                        (BExp_Den
                                           (BVar "SP_process"
                                              (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 20w)))
                                     BEnd_LittleEndian
                                     (BExp_Den
                                        (BVar "R4" (BType_Imm Bit32))))
                                  (BExp_BinExp BIExp_Minus
                                     (BExp_Den
                                        (BVar "SP_process"
                                           (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 16w)))
                                  BEnd_LittleEndian
                                  (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                               (BExp_BinExp BIExp_Minus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 12w)))
                               BEnd_LittleEndian
                               (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 566w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 566w) "200A (movs r0, #10)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Const (Imm32 10w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 568w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 568w) "B08F (sub sp, #60 ; 0x3c)";
                 bb_statements :=
                   [BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Align Bit32 2
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 60w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 570w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 570w)
                     "F7FFFF1F (bl 7c <AddRoundKey>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 575w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 124w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 574w) "2409 (movs r4, #9)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Const (Imm32 9w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 576w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 576w)
                     "F7FFFF88 (bl 154 <InvShiftRows>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 581w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 340w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 580w)
                     "F7FFFF71 (bl 7c <AddRoundKey>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 585w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 298w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 584w) "0020 (movs r0, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 586w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 586w)
                     "F7FFFF17 (bl 7c <AddRoundKey>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 591w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 124w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 590w)
                     "4B48 (ldr r3, [pc, #288] ; (370 <InvCipher+0x13c>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 880w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 592w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 592w)
                     "6B5D (ldr r5, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 594w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 594w) "002B (movs r3, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Den (BVar "R5" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 596w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 596w) "3310 (adds r3, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 598w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 598w)
                     "930D (str r3, [sp, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 600w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 600w) "782B (ldrb r3, [r5, #0])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 602w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 602w) "9304 (str r3, [sp, #16])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 604w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 604w) "786B (ldrb r3, [r5, #1])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 606w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 606w) "9804 (ldr r0, [sp, #16])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 608w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 608w) "9305 (str r3, [sp, #20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 610w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 610w) "78AB (ldrb r3, [r5, #2])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 612w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 612w) "9300 (str r3, [sp, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 614w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 614w) "78EB (ldrb r3, [r5, #3])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                            Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 616w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 616w) "9301 (str r3, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 618w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 618w) "F7FFFF57 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 623w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 622w) "9006 (str r0, [sp, #24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 24w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 24w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 624w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 624w) "F7FFFF54 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 629w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 628w) "9007 (str r0, [sp, #28])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 28w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 28w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 630w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 630w) "F7FFFF51 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 635w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 634w) "9002 (str r0, [sp, #8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 636w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 636w) "9805 (ldr r0, [sp, #20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 638w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 638w) "F7FFFF4D (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 643w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 642w) "9008 (str r0, [sp, #32])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 32w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 32w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 644w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 644w) "F7FFFF4A (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 649w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 648w)
                     "9009 (str r0, [sp, #36] ; 0x24)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 36w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 36w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 650w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 650w) "F7FFFF47 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 655w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 654w) "9003 (str r0, [sp, #12])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 656w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 656w) "9800 (ldr r0, [sp, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 658w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 658w) "F7FFFF43 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 663w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 662w)
                     "900A (str r0, [sp, #40] ; 0x28)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 40w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 40w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 664w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 664w) "F7FFFF40 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 669w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 668w) "0007 (movs r7, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Den (BVar "R0" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 670w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 670w) "F7FFFF3D (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 675w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 674w) "0006 (movs r6, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Den (BVar "R0" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 676w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 676w) "9801 (ldr r0, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 678w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 678w) "F7FFFF39 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 683w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 682w)
                     "900B (str r0, [sp, #44] ; 0x2c)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 44w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 44w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 684w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 684w) "F7FFFF36 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 689w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 688w)
                     "900C (str r0, [sp, #48] ; 0x30)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 48w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 48w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 690w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 690w) "F7FFFF33 (bl 11c <xtime>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 695w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 284w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 694w) "9A07 (ldr r2, [sp, #28])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 28w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 696w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 696w) "9B06 (ldr r3, [sp, #24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 24w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 698w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 698w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 700w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 700w) "9A02 (ldr r2, [sp, #8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 702w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 702w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 704w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 704w) "9A08 (ldr r2, [sp, #32])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 32w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 706w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 706w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 708w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 708w) "9A03 (ldr r2, [sp, #12])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 710w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 710w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 712w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 712w) "407B (eors r3, r7)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 714w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 714w) "9A05 (ldr r2, [sp, #20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 716w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 716w) "4073 (eors r3, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 718w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 718w) "4043 (eors r3, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 720w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 720w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 722w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 722w) "9A00 (ldr r2, [sp, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 724w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 724w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 726w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 726w) "9A01 (ldr r2, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 728w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 728w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 730w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 730w) "702B (strb r3, [r5, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 732w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 732w) "9A02 (ldr r2, [sp, #8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 734w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 734w) "9B08 (ldr r3, [sp, #32])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 32w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 736w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 736w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 738w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 738w)
                     "9A09 (ldr r2, [sp, #36] ; 0x24)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 36w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 740w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 740w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 742w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 742w) "9A03 (ldr r2, [sp, #12])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 744w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 744w) "9902 (ldr r1, [sp, #8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 746w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 746w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 748w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 748w)
                     "9A0A (ldr r2, [sp, #40] ; 0x28)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 40w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 750w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 750w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 752w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 752w)
                     "9A0C (ldr r2, [sp, #48] ; 0x30)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 48w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 754w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 754w) "4073 (eors r3, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 756w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 756w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 758w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 758w) "9A04 (ldr r2, [sp, #16])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 760w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 760w) "4043 (eors r3, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 762w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 762w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 764w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 764w) "9A00 (ldr r2, [sp, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 766w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 766w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 768w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 768w) "9A01 (ldr r2, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 770w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 770w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 772w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 772w) "706B (strb r3, [r5, #1])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 1w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 774w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 774w) "9A04 (ldr r2, [sp, #16])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 776w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 776w) "9B05 (ldr r3, [sp, #20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 778w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 778w) "4053 (eors r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 780w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 780w) "9A07 (ldr r2, [sp, #28])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 28w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 782w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 782w) "404A (eors r2, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 784w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 784w) "9903 (ldr r1, [sp, #12])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 786w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 786w) "404A (eors r2, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 788w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 788w)
                     "990A (ldr r1, [sp, #40] ; 0x28)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 40w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 790w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 790w) "404A (eors r2, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 792w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 792w) "4057 (eors r7, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 794w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 794w)
                     "9A0B (ldr r2, [sp, #44] ; 0x2c)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 44w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 796w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 796w) "4077 (eors r7, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R6" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 798w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 798w) "4057 (eors r7, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 800w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 800w) "9A01 (ldr r2, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 802w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 802w) "4047 (eors r7, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 804w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 804w) "4057 (eors r7, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 806w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 806w) "9902 (ldr r1, [sp, #8])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 808w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 808w) "9A06 (ldr r2, [sp, #24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 24w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 810w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 810w) "405F (eors r7, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 812w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 812w) "404A (eors r2, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 814w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 814w)
                     "9909 (ldr r1, [sp, #36] ; 0x24)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 36w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 816w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 816w) "70AF (strb r7, [r5, #2])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 2w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 818w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 818w) "404A (eors r2, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 820w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 820w) "9903 (ldr r1, [sp, #12])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 822w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 822w) "404A (eors r2, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 824w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 824w)
                     "990B (ldr r1, [sp, #44] ; 0x2c)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 44w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 826w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 826w) "4072 (eors r2, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 828w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 828w)
                     "9E0C (ldr r6, [sp, #48] ; 0x30)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 48w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 830w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 830w) "404A (eors r2, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 832w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 832w) "4056 (eors r6, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 834w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 834w) "9A00 (ldr r2, [sp, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 836w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 836w) "4070 (eors r0, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 838w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 838w) "4050 (eors r0, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 840w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 840w) "4058 (eors r0, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 842w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 842w)
                     "9B0D (ldr r3, [sp, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 844w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 844w) "70E8 (strb r0, [r5, #3])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 846w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 846w) "3504 (adds r5, #4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 4w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 848w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 848w) "42AB (cmp r3, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 850w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 850w)
                     "D181 (bne.n 258 <InvCipher+0x24>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 852w)))
                     (BLE_Label (BL_Address (Imm32 600w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 852w) "1E63 (subs r3, r4, #1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 854w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 854w) "B2DC (uxtb r4, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))) Bit8)
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 856w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 856w) "2C00 (cmp r4, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 858w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 858w)
                     "D000 (beq.n 35e <InvCipher+0x12a>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 862w)))
                     (BLE_Label (BL_Address (Imm32 860w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 860w)
                     "E770 (b.n 240 <InvCipher+0xc>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 576w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 862w)
                     "F7FFFEF9 (bl 154 <InvShiftRows>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 867w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 340w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 866w)
                     "F7FFFEE2 (bl 12a <InvSubBytes>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 871w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 298w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 870w) "0020 (movs r0, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 872w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 872w)
                     "F7FFFE88 (bl 7c <AddRoundKey>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 877w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 124w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 876w) "B00F (add sp, #60 ; 0x3c)";
                 bb_statements :=
                   [BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Align Bit32 2
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 60w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 878w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 878w)
                     "BDF0 (pop {r4, r5, r6, r7, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 16w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 20w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 884w)
                     "4B05 (ldr r3, [pc, #20] ; (38c <XorWithIv+0x18>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 908w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 886w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 886w) "B510 (push {r4, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) 8);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 8w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 888w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 888w)
                     "6B9C (ldr r4, [r3, #56] ; 0x38)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 56w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 890w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 890w) "2300 (movs r3, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Const (Imm32 0w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 892w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 892w) "5CC1 (ldrb r1, [r0, r3])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 894w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 894w) "5CE2 (ldrb r2, [r4, r3])";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                               (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                            BEnd_LittleEndian Bit8) Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 896w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 896w) "404A (eors r2, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_Xor
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Xor
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 898w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 898w) "54C2 (strb r2, [r0, r3])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))) 1);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R3" (BType_Imm Bit32))))
                         BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                            Bit8))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 900w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 900w) "3301 (adds r3, #1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 1w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 902w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 902w) "2B10 (cmp r3, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 904w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 904w)
                     "D1F8 (bne.n 37c <XorWithIv+0x8>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 906w)))
                     (BLE_Label (BL_Address (Imm32 892w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 906w) "BD10 (pop {r4, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 4w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 8w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 912w)
                     "B570 (push {r4, r5, r6, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) 16);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Store
                               (BExp_Store
                                  (BExp_Den
                                     (BVar "MEM" (BType_Mem Bit32 Bit8)))
                                  (BExp_BinExp BIExp_Minus
                                     (BExp_Den
                                        (BVar "SP_process"
                                           (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 16w)))
                                  BEnd_LittleEndian
                                  (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                               (BExp_BinExp BIExp_Minus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 12w)))
                               BEnd_LittleEndian
                               (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 914w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 914w) "0014 (movs r4, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Den (BVar "R2" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 916w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 916w) "000D (movs r5, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Den (BVar "R1" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 918w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 918w) "001A (movs r2, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Den (BVar "R3" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 920w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 920w) "0001 (movs r1, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Den (BVar "R0" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 922w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 922w) "0020 (movs r0, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 924w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 924w) "F7FFFFFE (bl 0 <memcpy>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 929w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 924w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 928w)
                     "4B04 (ldr r3, [pc, #16] ; (3b4 <AES_ECB_encrypt+0x24>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 948w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 930w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 930w)
                     "635C (str r4, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 932w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 932w)
                     "4B04 (ldr r3, [pc, #16] ; (3b4 <AES_ECB_encrypt+0x24>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 952w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 934w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 934w) "601D (str r5, [r3, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         BEnd_LittleEndian
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 936w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 936w)
                     "F7FFFE2A (bl 0 <KeyExpansion>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 941w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 940w) "F7FFFEF0 (bl 190 <Cipher>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 945w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 400w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 944w)
                     "BD70 (pop {r4, r5, r6, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 12w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 946w)
                     "46C0 (nop   ; (mov r8, r8))"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 948w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 956w)
                     "B570 (push {r4, r5, r6, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) 16);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Store
                               (BExp_Store
                                  (BExp_Den
                                     (BVar "MEM" (BType_Mem Bit32 Bit8)))
                                  (BExp_BinExp BIExp_Minus
                                     (BExp_Den
                                        (BVar "SP_process"
                                           (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 16w)))
                                  BEnd_LittleEndian
                                  (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                               (BExp_BinExp BIExp_Minus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 12w)))
                               BEnd_LittleEndian
                               (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 958w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 958w) "0014 (movs r4, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Den (BVar "R2" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 960w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 960w) "000D (movs r5, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Den (BVar "R1" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 962w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 962w) "001A (movs r2, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Den (BVar "R3" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 964w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 964w) "0001 (movs r1, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Den (BVar "R0" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 966w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 966w) "0020 (movs r0, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 968w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 968w) "F7FFFFFE (bl 0 <memcpy>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 973w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 968w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 972w)
                     "4B04 (ldr r3, [pc, #16] ; (3b4 <AES_ECB_encrypt+0x24>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 992w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 974w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 974w)
                     "635C (str r4, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 976w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 976w)
                     "4B04 (ldr r3, [pc, #16] ; (3b4 <AES_ECB_encrypt+0x24>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 996w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 978w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 978w) "601D (str r5, [r3, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         BEnd_LittleEndian
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 980w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 980w)
                     "F7FFFE14 (bl 0 <KeyExpansion>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 985w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 984w)
                     "F7FFFF2C (bl 234 <InvCipher>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 989w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 564w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 988w)
                     "BD70 (pop {r4, r5, r6, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 12w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 990w)
                     "46C0 (nop   ; (mov r8, r8))"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 992w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1000w)
                     "B5F7 (push {r0, r1, r2, r4, r5, r6, r7, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 32w))) 32);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 32w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Store
                               (BExp_Store
                                  (BExp_Store
                                     (BExp_Store
                                        (BExp_Store
                                           (BExp_Store
                                              (BExp_Den
                                                 (BVar "MEM"
                                                    (BType_Mem Bit32
                                                       Bit8)))
                                              (BExp_BinExp BIExp_Minus
                                                 (BExp_Den
                                                    (BVar "SP_process"
                                                       (BType_Imm Bit32)))
                                                 (BExp_Const (Imm32 32w)))
                                              BEnd_LittleEndian
                                              (BExp_Den
                                                 (BVar "R0"
                                                    (BType_Imm Bit32))))
                                           (BExp_BinExp BIExp_Minus
                                              (BExp_Den
                                                 (BVar "SP_process"
                                                    (BType_Imm Bit32)))
                                              (BExp_Const (Imm32 28w)))
                                           BEnd_LittleEndian
                                           (BExp_Den
                                              (BVar "R1"
                                                 (BType_Imm Bit32))))
                                        (BExp_BinExp BIExp_Minus
                                           (BExp_Den
                                              (BVar "SP_process"
                                                 (BType_Imm Bit32)))
                                           (BExp_Const (Imm32 24w)))
                                        BEnd_LittleEndian
                                        (BExp_Den
                                           (BVar "R2" (BType_Imm Bit32))))
                                     (BExp_BinExp BIExp_Minus
                                        (BExp_Den
                                           (BVar "SP_process"
                                              (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 20w)))
                                     BEnd_LittleEndian
                                     (BExp_Den
                                        (BVar "R4" (BType_Imm Bit32))))
                                  (BExp_BinExp BIExp_Minus
                                     (BExp_Den
                                        (BVar "SP_process"
                                           (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 16w)))
                                  BEnd_LittleEndian
                                  (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                               (BExp_BinExp BIExp_Minus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 12w)))
                               BEnd_LittleEndian
                               (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1002w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1002w) "9201 (str r2, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1004w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1004w) "220F (movs r2, #15)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Const (Imm32 15w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1006w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1006w) "000D (movs r5, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Den (BVar "R1" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1008w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1008w) "9901 (ldr r1, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1010w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1010w) "0006 (movs r6, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Den (BVar "R0" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1012w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1012w) "4011 (ands r1, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_And
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1014w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1014w) "9C08 (ldr r4, [sp, #32])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 32w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1016w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1016w) "9100 (str r1, [sp, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1018w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1018w) "2B00 (cmp r3, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1020w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1020w)
                     "D003 (beq.n 406 <AES_CBC_encrypt_buffer+0x1e>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 1030w)))
                     (BLE_Label (BL_Address (Imm32 1022w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1022w)
                     "4A15 (ldr r2, [pc, #84] ; (454 <AES_CBC_encrypt_buffer+0x6c>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 1108w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1024w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1024w) "6013 (str r3, [r2, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1026w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1026w)
                     "F7FFFDFD (bl 0 <KeyExpansion>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1031w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1030w) "2C00 (cmp r4, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1032w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1032w)
                     "D001 (beq.n 40e <AES_CBC_encrypt_buffer+0x26>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 1038w)))
                     (BLE_Label (BL_Address (Imm32 1034w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1034w)
                     "4B13 (ldr r3, [pc, #76] ; (458 <AES_CBC_encrypt_buffer+0x70>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 1112w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1036w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1036w)
                     "639C (str r4, [r3, #56] ; 0x38)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 56w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 56w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1038w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1038w) "0034 (movs r4, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R6" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Den (BVar "R6" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1040w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1040w) "9A01 (ldr r2, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1042w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1042w) "1BA3 (subs r3, r4, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1044w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1044w) "429A (cmp r2, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1046w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1046w)
                     "D90F (bls.n 438 <AES_CBC_encrypt_buffer+0x50>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp
                     (BExp_BinExp BIExp_Or
                        (BExp_UnaryExp BIExp_Not
                           (BExp_Den (BVar "PSR_C" BType_Bool)))
                        (BExp_Den (BVar "PSR_Z" BType_Bool)))
                     (BLE_Label (BL_Address (Imm32 1080w)))
                     (BLE_Label (BL_Address (Imm32 1048w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1048w) "0028 (movs r0, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R5" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1050w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1050w)
                     "F7FFFFAB (bl 374 <XorWithIv>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1055w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 884w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1054w) "0029 (movs r1, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Den (BVar "R5" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1056w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1056w) "2210 (movs r2, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Const (Imm32 16w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1058w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1058w) "0020 (movs r0, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1060w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1060w) "F7FFFFFE (bl 0 <memcpy>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1065w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1060w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1064w)
                     "4F0B (ldr r7, [pc, #44] ; (458 <AES_CBC_encrypt_buffer+0x70>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 1112w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1066w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1066w) "3510 (adds r5, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1068w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1068w)
                     "637C (str r4, [r7, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1070w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1070w)
                     "F7FFFEAF (bl 190 <Cipher>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1075w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 400w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1074w)
                     "63BC (str r4, [r7, #56] ; 0x38)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 56w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 56w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1076w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1076w) "3410 (adds r4, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1078w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1078w)
                     "E7EB (b.n 410 <AES_CBC_encrypt_buffer+0x28>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1040w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1080w) "9B00 (ldr r3, [sp, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1082w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1082w) "2B00 (cmp r3, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1084w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1084w)
                     "D008 (beq.n 450 <AES_CBC_encrypt_buffer+0x68>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 1104w)))
                     (BLE_Label (BL_Address (Imm32 1086w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1086w) "001A (movs r2, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Den (BVar "R3" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1088w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1088w) "0029 (movs r1, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Den (BVar "R5" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1090w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1090w) "0020 (movs r0, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1092w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1092w) "F7FFFFFE (bl 0 <memcpy>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1097w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1092w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1096w)
                     "4B03 (ldr r3, [pc, #12] ; (458 <AES_CBC_encrypt_buffer+0x70>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 1112w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1098w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1098w)
                     "635C (str r4, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1100w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1100w)
                     "F7FFFEA0 (bl 190 <Cipher>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1105w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 400w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1104w)
                     "BDF7 (pop {r0, r1, r2, r4, r5, r6, r7, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 28w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 28w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 24w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 32w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1106w)
                     "46C0 (nop   ; (mov r8, r8))"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1108w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1116w)
                     "B5F7 (push {r0, r1, r2, r4, r5, r6, r7, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 32w))) 32);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 32w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Store
                               (BExp_Store
                                  (BExp_Store
                                     (BExp_Store
                                        (BExp_Store
                                           (BExp_Store
                                              (BExp_Den
                                                 (BVar "MEM"
                                                    (BType_Mem Bit32
                                                       Bit8)))
                                              (BExp_BinExp BIExp_Minus
                                                 (BExp_Den
                                                    (BVar "SP_process"
                                                       (BType_Imm Bit32)))
                                                 (BExp_Const (Imm32 32w)))
                                              BEnd_LittleEndian
                                              (BExp_Den
                                                 (BVar "R0"
                                                    (BType_Imm Bit32))))
                                           (BExp_BinExp BIExp_Minus
                                              (BExp_Den
                                                 (BVar "SP_process"
                                                    (BType_Imm Bit32)))
                                              (BExp_Const (Imm32 28w)))
                                           BEnd_LittleEndian
                                           (BExp_Den
                                              (BVar "R1"
                                                 (BType_Imm Bit32))))
                                        (BExp_BinExp BIExp_Minus
                                           (BExp_Den
                                              (BVar "SP_process"
                                                 (BType_Imm Bit32)))
                                           (BExp_Const (Imm32 24w)))
                                        BEnd_LittleEndian
                                        (BExp_Den
                                           (BVar "R2" (BType_Imm Bit32))))
                                     (BExp_BinExp BIExp_Minus
                                        (BExp_Den
                                           (BVar "SP_process"
                                              (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 20w)))
                                     BEnd_LittleEndian
                                     (BExp_Den
                                        (BVar "R4" (BType_Imm Bit32))))
                                  (BExp_BinExp BIExp_Minus
                                     (BExp_Den
                                        (BVar "SP_process"
                                           (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 16w)))
                                  BEnd_LittleEndian
                                  (BExp_Den (BVar "R5" (BType_Imm Bit32))))
                               (BExp_BinExp BIExp_Minus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 12w)))
                               BEnd_LittleEndian
                               (BExp_Den (BVar "R6" (BType_Imm Bit32))))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R7" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1118w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1118w) "9201 (str r2, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1120w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1120w) "220F (movs r2, #15)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Const (Imm32 15w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1122w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1122w) "000D (movs r5, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Den (BVar "R1" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1124w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1124w) "9901 (ldr r1, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1126w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1126w) "0006 (movs r6, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Den (BVar "R0" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1128w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1128w) "4011 (ands r1, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32)))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                            (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_And
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1130w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1130w) "9C08 (ldr r4, [sp, #32])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 32w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1132w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1132w) "9100 (str r1, [sp, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1134w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1134w) "2B00 (cmp r3, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1136w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1136w)
                     "D003 (beq.n 406 <AES_CBC_encrypt_buffer+0x1e>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 1146w)))
                     (BLE_Label (BL_Address (Imm32 1138w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1138w)
                     "4A15 (ldr r2, [pc, #84] ; (454 <AES_CBC_encrypt_buffer+0x6c>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 1224w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1140w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1140w) "6013 (str r3, [r2, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         BEnd_LittleEndian
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1142w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1142w)
                     "F7FFFDC3 (bl 0 <KeyExpansion>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1147w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1146w) "2C00 (cmp r4, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1148w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1148w)
                     "D001 (beq.n 40e <AES_CBC_encrypt_buffer+0x26>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 1154w)))
                     (BLE_Label (BL_Address (Imm32 1150w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1150w)
                     "4B13 (ldr r3, [pc, #76] ; (458 <AES_CBC_encrypt_buffer+0x70>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 1228w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1152w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1152w)
                     "639C (str r4, [r3, #56] ; 0x38)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 56w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 56w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1154w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1154w) "0034 (movs r4, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R6" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Den (BVar "R6" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1156w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1156w) "9A01 (ldr r2, [sp, #4])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1158w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1158w) "1BA3 (subs r3, r4, r6)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R6" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1160w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1160w) "429A (cmp r2, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1162w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1162w)
                     "D90F (bls.n 438 <AES_CBC_encrypt_buffer+0x50>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp
                     (BExp_BinExp BIExp_Or
                        (BExp_UnaryExp BIExp_Not
                           (BExp_Den (BVar "PSR_C" BType_Bool)))
                        (BExp_Den (BVar "PSR_Z" BType_Bool)))
                     (BLE_Label (BL_Address (Imm32 1196w)))
                     (BLE_Label (BL_Address (Imm32 1164w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1164w) "0029 (movs r1, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Den (BVar "R5" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1166w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1166w) "2210 (movs r2, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Const (Imm32 16w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1168w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1168w) "0020 (movs r0, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1170w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1170w) "F7FFFFFE (bl 0 <memcpy>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1175w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1170w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1174w)
                     "4F0D (ldr r7, [pc, #52] ; (4cc <AES_CBC_decrypt_buffer+0x70>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 1228w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1176w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1176w)
                     "637C (str r4, [r7, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1178w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1178w)
                     "F7FFFECB (bl 234 <InvCipher>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1183w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 564w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1182w) "0020 (movs r0, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1184w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1184w)
                     "F7FFFF68 (bl 374 <XorWithIv>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1189w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 884w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1188w) "3410 (adds r4, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1190w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1190w)
                     "63BD (str r5, [r7, #56] ; 0x38)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R7" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 56w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R7" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 56w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1192w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1192w) "3510 (adds r5, #16)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_ADD_C
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_ADD_N Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_ADD_V Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_ADD_Z
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)));
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 16w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1194w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1194w)
                     "E7EB (b.n 410 <AES_CBC_encrypt_buffer+0x28>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1156w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1196w) "9B00 (ldr r3, [sp, #0])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1198w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1198w) "2B00 (cmp r3, #0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool) bir_exp_true;
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool) bir_exp_false;
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1200w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1200w)
                     "D008 (beq.n 450 <AES_CBC_encrypt_buffer+0x68>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 1220w)))
                     (BLE_Label (BL_Address (Imm32 1202w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1202w) "001A (movs r2, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Den (BVar "R3" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1204w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1204w) "0029 (movs r1, r5)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R5" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R5" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Den (BVar "R5" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1206w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1206w) "0020 (movs r0, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1208w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1208w) "F7FFFFFE (bl 0 <memcpy>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1213w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1208w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1212w)
                     "4B03 (ldr r3, [pc, #12] ; (458 <AES_CBC_encrypt_buffer+0x70>))";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Const (Imm32 1228w)) BEnd_LittleEndian
                         Bit32)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1214w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1214w)
                     "635C (str r4, [r3, #52] ; 0x34)";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 65536
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 52w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1216w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1216w)
                     "F7FFFEB8 (bl 234 <InvCipher>)";
                 bb_statements :=
                   [BStmt_Assign (BVar "LR" (BType_Imm Bit32))
                      (BExp_Const (Imm32 1221w))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 564w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1220w)
                     "BDF7 (pop {r0, r1, r2, r4, r5, r6, r7, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 28w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 28w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 12w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R5" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R6" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "R7" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 24w))) BEnd_LittleEndian
                         Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 32w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 1222w)
                     "46C0 (nop   ; (mov r8, r8))"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 1224w)))|>])


*)
end
