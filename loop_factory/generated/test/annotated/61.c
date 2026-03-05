int main1(int h,int t){
  int vk, y8, jk;
  vk=62;
  y8=0;
  jk=y8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y8 == 0;
  loop invariant vk == 62;
  loop invariant t == \at(t, Pre);
  loop invariant jk >= 0;
  loop invariant h - \at(h, Pre) == (jk*(jk+1))/2;
  loop assigns h, jk;
*/
while (y8+1<=vk) {
      jk = jk + 1;
      h = h + jk;
  }
}