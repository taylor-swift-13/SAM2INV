int main1(){
  int kb, ru2, ak8;
  kb=1*3;
  ru2=0;
  ak8=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ru2 == ak8;
  loop invariant 0 <= ak8;
  loop invariant ak8 <= kb;
  loop assigns ru2, ak8;
*/
while (1) {
      if (!(ak8<=kb-1)) {
          break;
      }
      ru2 += 1;
      ak8 += 1;
  }
}