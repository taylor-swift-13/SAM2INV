int main1(int n,int q){
  int h, d, w;

  h=26;
  d=h;
  w=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 26;
  loop invariant w >= 26;
  loop invariant d >= 0;
  loop invariant w % 2 == 0;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= d <= 26;
  loop invariant 0 <= d;
  loop invariant d <= 26;
  loop invariant w >= 0;
  loop invariant w >= h;
  loop assigns w, d;
*/
while (d>0) {
      w = w*2;
      if (w+5<h) {
          w = w*w+w;
      }
      else {
          w = w*2;
      }
      d = d-1;
  }

}
