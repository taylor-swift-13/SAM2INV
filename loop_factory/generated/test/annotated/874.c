int main1(int s){
  int vk, a, vdh;
  vk=63;
  a=vk;
  vdh=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vk == 63;
  loop invariant (a == 63) || (a == 0);
  loop invariant vdh >= 4;
  loop invariant 0 <= a;
  loop invariant s == \at(s, Pre) + (63 - a);
  loop assigns s, a, vdh;
*/
while (a>0) {
      vdh++;
      s = s + a;
      a = 0;
  }
}