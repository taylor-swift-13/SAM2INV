int main1(int p,int b){
  int grw, vb, d, v, hw;
  grw=p-8;
  vb=grw;
  d=20;
  v=1;
  hw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == hw + 1;
  loop invariant vb == grw + hw;
  loop invariant 0 <= hw;
  loop invariant d <= 20;
  loop assigns d, vb, v, hw;
*/
while (d>0&&v<=grw) {
      if (!(d<=v)) {
          d = 0;
      }
      else {
          d -= v;
      }
      vb = vb + 1;
      v++;
      hw++;
  }
}