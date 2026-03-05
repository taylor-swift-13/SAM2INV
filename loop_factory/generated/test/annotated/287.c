int main1(int l){
  int jr, ox3, i0;
  jr=l-9;
  ox3=0;
  i0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i0 > 0 ==> i0 <= jr;
  loop invariant l == \at(l, Pre);
  loop invariant ox3 >= i0;
  loop invariant 0 <= i0 <= 1;
  loop invariant jr == \at(l, Pre) - 9;
  loop assigns i0, ox3;
*/
while (i0>0&&i0<=jr) {
      if (i0>i0) {
          i0 = i0 - i0;
      }
      else {
          i0 = 0;
      }
      i0 = i0 + 1;
      ox3 = ox3 + 1;
  }
}