int main1(int z){
  int voll, xn;
  voll=66;
  xn=voll;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant voll == 66;
  loop invariant (voll - xn) >= 0;
  loop invariant z == \at(z, Pre);
  loop invariant 0 <= xn;
  loop invariant (66 - xn) % 6 == 0;
  loop assigns xn;
*/
for (; xn>5; xn -= 6) {
  }
}