int main1(){
  int qr, m, i, ow, t6d;
  qr=(1%35)+13;
  m=0;
  i=0;
  ow=0;
  t6d=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ow == i*m + i*t6d + i*(i+1)/2;
  loop invariant i + t6d == 4;
  loop invariant 0 <= t6d <= 4;
  loop invariant m == 0;
  loop invariant qr == 14;
  loop assigns ow, i, t6d;
*/
while (i<qr&&t6d>0) {
      ow += t6d;
      i = i + 1;
      ow = ow + m;
      t6d--;
  }
}