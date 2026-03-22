int main1(int i){
  int h, a1, mod, jt, g;
  h=i+19;
  a1=1;
  mod=a1;
  jt=a1;
  g=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a1 == 1;
  loop invariant mod >= 1;
  loop invariant h == \at(i,Pre) + 19 || h == (2*a1) - 1;
  loop invariant i == \at(i, Pre);
  loop invariant (jt == 1) ==> (mod == 1);
  loop invariant g >= 5;
  loop invariant 0 <= jt <= 1;
  loop assigns jt, mod, g, h;
*/
while (a1*2<=h) {
      jt = jt/4;
      mod = mod*4;
      g = g*3+(jt%6)+0;
      h = (a1*2)-1;
  }
}