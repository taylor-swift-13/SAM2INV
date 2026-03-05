int main1(int i,int a){
  int erx, zi, hv0;
  erx=(i%22)+8;
  zi=erx;
  hv0=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zi == (\at(i,Pre) % 22) + 8;
  loop invariant a == \at(a,Pre);
  loop invariant (hv0 == 1) || (hv0 == 2);
  loop invariant i >= \at(i,Pre);
  loop invariant erx == (\at(i, Pre) % 22) + 8;
  loop assigns i, hv0;
*/
while (zi-1>=0) {
      if (hv0==1) {
          hv0 = 2;
      }
      else {
          if (hv0==2) {
              hv0 = 1;
          }
      }
      i += hv0;
      i = i + 3;
  }
}