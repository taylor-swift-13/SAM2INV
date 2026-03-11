int main1(int k,int t){
  int obx, h8;
  obx=31;
  h8=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= h8 <= obx;
  loop invariant (h8 % 4) == 0;
  loop invariant k == \at(k, Pre) + (h8 / 4) * \at(t, Pre);
  loop invariant k == \at(k,Pre) + (h8/4) * t;
  loop invariant k == \at(k,Pre) + t * (h8 / 4);
  loop assigns k, h8;
*/
for (; h8<=obx-4; h8 += 4) {
      k += t;
  }
}