int main1(){
  int ax, w, y, yt;
  ax=1*4;
  w=0;
  y=w;
  yt=ax;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w <= ax;
  loop invariant yt >= ax;
  loop invariant ((yt - ax) % 2) == 0;
  loop invariant y == ((yt - ax) / 2) * ax  + ((yt - ax) / 2) * (((yt - ax) / 2) + 1);
  loop invariant ax == 4 &&
                   0 <= w && w <= ax;
  loop invariant y >= 0;
  loop assigns w, yt, y;
*/
while (w < ax) {
      w = w + 1 + (ax - w) / 2;
      yt += 2;
      y = y + yt;
  }
}