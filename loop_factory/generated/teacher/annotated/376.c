int main1(int k,int m){
  int h, c, y, v;

  h=m;
  c=h+4;
  y=c;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == m;
  loop invariant c == h + 4;
  loop invariant c >= h;
  loop invariant y >= c;
  loop invariant ((y - c) % 2) == 0;
  loop invariant (c == h + 4);
  loop invariant (k == \at(k, Pre));
  loop invariant (m == \at(m, Pre));
  loop invariant (y >= c);
  loop invariant (((y - c) % 2) == 0);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant y >= \at(m, Pre) + 4;
  loop invariant ((y - (\at(m, Pre) + 4)) % 2 == 0);
  loop invariant y >= h + 4;
  loop invariant (y - h) % 2 == 0;
  loop invariant (v == k && y == m + 4) || (y - v == 2);
  loop assigns v, y;
*/
while (c>h) {
      v = y;
      y = y+2;
  }

}
