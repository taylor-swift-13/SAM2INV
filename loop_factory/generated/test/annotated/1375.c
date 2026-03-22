int main1(){
  int shj, pb, hy;
  shj=1*5;
  pb=0;
  hy=shj;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant shj == 5;
  loop invariant hy % 5 == 0;
  loop invariant pb <= shj;
  loop invariant hy >= 5;
  loop invariant (pb == 0)  ==> (hy == shj);
  loop invariant 0 <= pb;
  loop assigns hy, pb;
*/
for (; pb<=shj-1; pb = pb + 1) {
      hy = hy*2;
  }
}