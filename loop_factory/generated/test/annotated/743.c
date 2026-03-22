int main1(int z,int k){
  int d6, f;
  d6=0;
  f=(z%28)+10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d6 >= 0;
  loop invariant f == (\at(z, Pre) % 28) + 10 - (d6 * (d6 - 1)) / 2;
  loop invariant k == \at(k, Pre);
  loop assigns d6, f, z;
*/
while (f>d6) {
      f -= d6;
      d6 = (1)+(d6);
      z += f;
  }
}