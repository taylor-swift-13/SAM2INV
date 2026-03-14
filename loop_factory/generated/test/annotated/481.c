int main1(int p){
  int uk, azjh, l1, y, t4q;
  uk=0;
  azjh=0;
  l1=0;
  y=0;
  t4q=(p%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t4q <= ((\at(p, Pre) % 18) + 5);
  loop invariant y == l1;
  loop invariant azjh == y;
  loop invariant y == p*p * ( ((\at(p, Pre) % 18) + 5) - t4q );
  loop invariant p == \at(p, Pre);
  loop invariant uk == 0;
  loop invariant l1 >= 0;
  loop assigns y, l1, t4q, azjh, p;
*/
while (1) {
      if (!(t4q>=1)) {
          break;
      }
      y = y+p*p;
      l1 = l1+p*p;
      t4q = t4q - 1;
      azjh = azjh+p*p;
      p += uk;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uk >= 0;
  loop invariant p >= \at(p, Pre);
  loop invariant l1 >= 0;
  loop invariant y >= 0;
  loop assigns l1, y, uk, p;
*/
while (l1>y) {
      l1 = l1 - y;
      y = (1)+(y);
      uk = uk+(l1%3);
      p = p + l1;
  }
}