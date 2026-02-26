int main1(int a,int m){
  int k, i, h, v;

  k=24;
  i=0;
  h=3;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant k == 24;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v == 0;
  loop invariant h >= 3;
  loop assigns h, v;
*/
while (1) {
      if (i<k/2) {
          h = h+v;
      }
      else {
          h = h+1;
      }
      h = h+1;
      v = v+h;
      if ((i%6)==0) {
          v = h-v;
      }
      else {
          h = v-h;
      }
      v = v+i;
  }

}
