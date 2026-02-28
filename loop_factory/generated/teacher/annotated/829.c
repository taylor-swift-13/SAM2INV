int main1(int k,int n,int p){
  int e, t, f, d, v, w;

  e=(n%8)+16;
  t=0;
  f=0;
  d=1;
  v=6;
  w=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v == 6 + 2*w;
  loop invariant d == w*w + 5*w + 1;
  loop invariant 3*f == w*w*w + 6*w*w - 4*w;
  loop invariant w >= 0;
  loop invariant w <= e + 1;
  loop invariant f == (w*w*w + 6*w*w - 4*w)/3;
  loop invariant e == (\at(n, Pre) % 8) + 16;
  loop invariant f == w*(w*w + 6*w - 4)/3;

  loop invariant 0 <= w <= e + 1;
  loop assigns w, f, d, v;
*/
while (w<=e) {
      w = w+1;
      f = f+d;
      d = d+v;
      v = v+2;
  }

}
