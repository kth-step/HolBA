signature aesTheory =
sig
  type thm = Thm.thm

  (*  Theorems  *)
    val aes_program_THM : thm

  val aes_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bir_inst_lifting] Parent theory of "aes"

   [aes_program_THM]  Theorem

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
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "ProcState_V" BType_Bool)
                      bir_exp_false;
                    BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                         (BExp_Const (Imm32 0w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4009C8w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4009C8w)
                     "54FFE321 (b.ne 0x40062c)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_IfThenElse
                           (BExp_Den (BVar "ProcState_Z" BType_Bool))
                           (BExp_Const (Imm64 0x4009CCw))
                           (BExp_BinExp BIExp_Minus
                              (BExp_Const (Imm64 0x4009C8w))
                              (BExp_Const (Imm64 924w)))))|>;
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


*)
end
