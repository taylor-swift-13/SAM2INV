int main1(int e,int x){
  int avl, z, s, s5o, xj, gz8, i4;
  avl=e;
  z=0;
  s=avl;
  s5o=avl;
  xj=z;
  gz8=z;
  i4=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant avl == e;
  loop invariant i4 == e;
  loop invariant 0 <= gz8;
  loop invariant xj == 6 * gz8;
  loop invariant s5o == avl + 3 * gz8 * (gz8 - 1);
  loop invariant s == avl * (gz8 + 1) + (gz8 - 1) * gz8 * (gz8 - 2);
  loop assigns s, s5o, gz8, xj, i4;
*/
while (1) {
      if (gz8>avl) {
          break;
      }
      s = s + s5o;
      s5o += xj;
      gz8 += 1;
      xj = (6)+(xj);
      i4 = i4+(xj%6);
  }
}