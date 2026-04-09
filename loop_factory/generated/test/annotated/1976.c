int main1(){
  int l, k3u5, f6, f, fx;
  l=29;
  k3u5=0;
  f6=k3u5;
  f=k3u5;
  fx=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= k3u5);
  loop invariant (k3u5 <= l);
  loop invariant (fx == l);
  loop invariant (f6 == (fx * k3u5));
  loop invariant (f == (k3u5 * (l + 1)));
  loop assigns k3u5, f6, f;
*/
while (k3u5 < l) {
      k3u5++;
      f6 += fx;
      f += l;
      f = f + 1;
  }
}