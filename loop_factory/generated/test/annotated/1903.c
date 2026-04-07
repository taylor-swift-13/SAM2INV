int main1(){
  int l, bt, mu, ur, y12, u, b, t75r;
  l=102;
  bt=0;
  mu=l;
  ur=4;
  y12=bt;
  u=0;
  b=25;
  t75r=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bt == 0;
  loop invariant l <= 102;
  loop invariant ur >= 0;
  loop invariant y12 >= 0;
  loop invariant l >= bt + 3;
  loop invariant (mu == 102);
  loop invariant b <= 25;
  loop invariant t75r <= 0;
  loop invariant u <= 0;
  loop assigns mu, ur, y12, b, t75r, u, l;
*/
while (bt+4<=l) {
      if (bt%3==2) {
          mu++;
      }
      else {
          ur = ur + 1;
      }
      if (bt%3==0) {
          y12++;
      }
      else {
      }
      b += bt;
      b += t75r;
      t75r = (u)+(t75r);
      if (b+2<l) {
          b = b + u;
      }
      else {
          u += t75r;
      }
      l = (bt+4)-1;
  }
}