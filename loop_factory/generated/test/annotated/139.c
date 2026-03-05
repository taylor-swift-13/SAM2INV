int main1(){
  int al, ph, pcm4, ojpc;
  al=1;
  ph=0;
  pcm4=10;
  ojpc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ph <= al;
  loop invariant pcm4 >= 10;
  loop invariant ojpc >= 0;
  loop invariant al == 1;
  loop invariant ph >= 0;
  loop assigns ph, pcm4, ojpc;
*/
while (ph<al) {
      if (ph%2==0) {
          if (pcm4>0) {
              pcm4--;
              ojpc += 1;
          }
      }
      else {
          if (ojpc>0) {
              ojpc = ojpc - 1;
              pcm4 = pcm4 + 1;
          }
      }
      ph = ph + 1;
      pcm4 = pcm4 + 1;
      ojpc += 1;
  }
}