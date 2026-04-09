int main1(){
  int wr, vk, a8s, a4;
  wr=13;
  vk=wr;
  a8s=0;
  a4=wr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (vk <= wr);
  loop invariant a8s == 3*(vk - wr);
  loop invariant 2*(a4 - wr) == (vk - wr)*(2*wr + (vk - wr) + 1);
  loop invariant 2*a4 == (vk * vk) + vk - (wr * wr) + wr;
  loop invariant 13 <= vk;
  loop invariant a8s == 3 * (vk - 13);
  loop invariant a4 == 13 + (vk - 13) * 13 + ((vk - 13) * ((vk - 13) + 1)) / 2;
  loop invariant a4 == wr + (vk - wr) * wr + ((vk - wr) * ((vk - wr) + 1)) / 2;
  loop assigns a8s, vk, a4;
*/
while (1) {
      if (vk>=wr) {
          break;
      }
      a8s = a8s + 3;
      vk = vk + 1;
      a4 = a4 + vk;
  }
}