int main1(){
  int vz, emo, zdq, cd9, sm2;
  vz=71;
  emo=0;
  zdq=emo;
  cd9=3;
  sm2=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sm2 == 5;
  loop invariant cd9 == 3 + emo * sm2;
  loop invariant zdq == 3*emo + sm2 * (emo * (emo - 1) / 2);
  loop invariant (0 <= emo && emo <= vz);
  loop assigns emo, zdq, cd9;
*/
while (1) {
      if (!(emo < vz)) {
          break;
      }
      emo = emo + 1;
      zdq += cd9;
      cd9 += sm2;
  }
}