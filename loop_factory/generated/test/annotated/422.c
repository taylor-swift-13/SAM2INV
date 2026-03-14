int main1(int u,int b){
  int ke6, fq94, hqca;
  ke6=u;
  fq94=0;
  hqca=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fq94 % 7 == 0;
  loop invariant hqca == 4 + fq94/7;
  loop invariant fq94 >= 0;
  loop invariant ke6 == u;
  loop assigns fq94, hqca;
*/
for (; fq94+7<=ke6; fq94 = fq94 + 7) {
      hqca += 1;
  }
}