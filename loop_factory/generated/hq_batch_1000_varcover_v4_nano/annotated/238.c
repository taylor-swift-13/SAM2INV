int main1(int m,int n,int p){
  int l, i, v, x, t, y, s;

  l=(m%6)+9;
  i=l;
  v=n;
  x=i;
  t=n;
  y=-5;
  s=p;

  
  /*@

    loop invariant l == (m%6) + 9;

    loop invariant 0 <= i && i <= l;

    loop invariant t + 2 * i == n + 2 * l;

    loop invariant v - 4 * (l - i) == n;

    loop invariant x + i == 2 * l;

    loop invariant ((l - i) % 2 == 0 ==> y == -5) && ((l - i) % 2 != 0 ==> y == s + 5);

    loop assigns v, t, y, x, i;

    loop variant i;

  */
while (i>0) {
      v = v+4;
      t = t+1;
      t = t+1;
      y = s-y;
      if (v<v+1) {
          x = x+1;
      }
      i = i-1;
  }

}