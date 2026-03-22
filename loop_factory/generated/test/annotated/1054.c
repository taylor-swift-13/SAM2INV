int main1(){
  int d, i8, bvb2, dtce, i, xhf;
  d=1*5;
  i8=1;
  bvb2=0;
  dtce=0;
  i=1*4;
  xhf=i8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dtce == bvb2;
  loop invariant dtce <= d;
  loop invariant i >= 4;
  loop invariant 0 <= dtce;
  loop assigns dtce, bvb2, i;
*/
while (1) {
      if (!(dtce<d)) {
          break;
      }
      dtce += 1;
      bvb2++;
      i += bvb2;
      i = i*3+4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i8 >= 1;
  loop invariant i >= 4;
  loop invariant xhf >= 1;
  loop assigns i, i8, xhf;
*/
while (xhf>1) {
      if (xhf%2==0) {
          i8 = i8 + i;
      }
      else {
          i8 = i8+i+1;
      }
      i += xhf;
      xhf = 1;
  }
}