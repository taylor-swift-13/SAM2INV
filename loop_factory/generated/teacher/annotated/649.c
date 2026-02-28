int main1(int b,int k){
  int h, s, p, v, r, a;

  h=(k%27)+11;
  s=h;
  p=8;
  v=-2;
  r=s;
  a=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r - 6*a == -5*h;
  loop invariant a <= h + 1;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant s == h;
  loop invariant r == 6*a - 5*h;
  loop invariant v == -2 + (a - h)*(h - 3) + 3*(a - h)*(a - h);
  loop invariant p == 8 + (a - h)*(h - 2) + ((a - h)*(a - h - 1)/2)*(2*a - h - 4);

  loop invariant r - 6*a == s - 6*h;
  loop invariant a >= h;
  loop invariant p == 8 - 2*(a - h) + h*(a - h)*(a - h + 1)/2 + (a - h)*(a - h - 1)*(a - h - 2);
  loop invariant h == (k % 27) + 11;

  loop invariant p == 8 + (a - h)*(h - 2) + ((a - h)*(a - h - 1)/2) * (h + 2*(a - h) - 4);
  loop assigns p, v, r, a;
*/
while (a<=h) {
      p = p+v;
      v = v+r;
      r = r+6;
      a = a+1;
      p = p+s;
  }

}
