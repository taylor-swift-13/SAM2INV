int main1(int a,int b,int k,int p){
  int i, m, w, v, d, f, x, g;

  i=k;
  m=0;
  w=a;
  v=4;
  d=-8;
  f=5;
  x=-6;
  g=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w - f == a - 5;
  loop invariant i == \at(k, Pre);
  loop invariant m == 0;
  loop invariant x == -6;
  loop invariant w >= a;
  loop invariant f == 5 + (w - a);
  loop invariant -8 <= v;
  loop invariant v <= 4;
  loop invariant i == k;
  loop invariant f >= 5;
  loop invariant d == -8;
  loop assigns w, v, f, x;
*/
while (1) {
      if (d<=v) {
          v = d;
      }
      w = w+1;
      v = v-1;
      f = f+1;
      x = x+m;
      v = v+4;
  }

}
