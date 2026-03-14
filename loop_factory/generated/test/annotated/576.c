int main1(int v,int g){
  int ny, d, hti, ys, pq;
  ny=8;
  d=1;
  hti=0;
  ys=0;
  pq=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (hti == 0) ==> (d == 1);
  loop invariant (hti > 0) ==> (d % 2 == 0);
  loop invariant ny == 8;
  loop invariant g == \at(g, Pre);
  loop invariant v == \at(v, Pre);
  loop invariant pq >= 11;
  loop invariant ys >= 0;
  loop invariant hti >= 0;
  loop invariant (hti >= 2) ==> (d % 4 == 0);
  loop invariant (hti >= 3) ==> (d % 8 == 0);
  loop invariant d >= 1;
  loop assigns d, hti, pq, ys;
*/
while (d<=ny) {
      d = 2*d;
      hti++;
      pq = pq*3+(d%4)+0;
      ys = ys*4+(d%6)+3;
  }
}