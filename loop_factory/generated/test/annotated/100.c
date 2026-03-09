int main1(int l,int r){
  int k93, kr, j;
  k93=r;
  kr=0;
  j=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == \at(l,Pre) + kr * (kr + 1) / 2;
  loop invariant k93 == \at(r,Pre);
  loop invariant kr >= 0;
  loop invariant j >= 3;
  loop assigns j, kr, l;
*/
while (kr<k93) {
      if (kr>=k93/2) {
          j += 2;
      }
      kr += 1;
      l = l + kr;
  }
}