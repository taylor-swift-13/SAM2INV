int main1(int m,int p){
  int i, t, w, n;

  i=10;
  t=0;
  w=-5;
  n=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 3*w + 15;
  loop invariant w + n == -6;
  loop invariant t >= 0;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant t == 3*(w + 5);

  loop invariant i == 10;
  loop invariant m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant t % 3 == 0;
  loop invariant t <= i + 2;
  loop invariant n <= -1;
  loop invariant n + w == -6;
  loop invariant i == 10 && m == \at(m, Pre) && p == \at(p, Pre) && t <= i + 2;
  loop invariant n == -w - 6 && m == \at(m, Pre) && p == \at(p, Pre) && i == 10;
  loop invariant t == 3*(w + 5) && n + w == -6 && t >= 0 && w >= -5;
  loop invariant t + 3*n + 3 == 0;
  loop invariant n + w == -6 && t <= i + 2 && m == \at(m, Pre) && p == \at(p, Pre);
  loop assigns w, n, t;
*/
while (t<i) {
      w = w+1;
      n = n-1;
      t = t+3;
  }

}
