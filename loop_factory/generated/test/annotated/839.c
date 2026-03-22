int main1(){
  int k, izh, hw, ji, qle8, e;
  k=(1%34)+14;
  izh=0;
  hw=izh;
  ji=0;
  qle8=0;
  e=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (qle8 == 0) <==> (hw == 0);
  loop invariant ji == 0;
  loop invariant e == 3;
  loop invariant hw >= qle8;
  loop invariant qle8 <= k;
  loop invariant k == 15;
  loop invariant 0 <= qle8;
  loop assigns ji, qle8, hw, e;
*/
while (1) {
      if (qle8>=k) {
          break;
      }
      ji = ji*e;
      qle8 = qle8 + 1;
      hw = hw*e+1;
      e = e+(ji%6);
  }
}