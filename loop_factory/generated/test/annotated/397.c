int main1(){
  int z1d, qbf, a1, o, cz;
  z1d=42;
  qbf=0;
  a1=0;
  o=5;
  cz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cz == qbf;
  loop invariant (qbf == 0) ==> (o == 5);
  loop invariant o % 4 == (qbf + 1) % 4;
  loop invariant z1d == 42;
  loop invariant 0 <= qbf <= z1d;
  loop invariant o >= 0;
  loop invariant a1 >= 0;
  loop invariant a1 <= qbf;
  loop assigns cz, o, a1, qbf;
*/
while (qbf<z1d) {
      cz += 1;
      o = o + 1;
      if (o>=4) {
          o -= 4;
          a1 += 1;
      }
      qbf++;
  }
}