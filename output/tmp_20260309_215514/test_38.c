int main1(){
  int xz, jjd, jp, l2, f, vk2;
  xz=1+7;
  jjd=xz;
  jp=-2;
  l2=0;
  f=xz;
  vk2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vk2 == jp + 2;
  loop invariant xz == 8;
  loop invariant jjd == 8;
  loop invariant 0 <= vk2;
  loop invariant jp <= xz;
  loop invariant f >= xz;
  loop assigns l2, jp, vk2, f;
*/
while (jp<xz) {
      l2 += jp;
      jp += 1;
      vk2 += 1;
      f += jjd;
      f = f + vk2;
  }
/*@
  assert (jp == 8) &&
         (vk2 == 10);
*/
}
