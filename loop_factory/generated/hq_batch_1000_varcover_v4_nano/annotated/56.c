int main1(int b,int k,int n){
  int l, i, v, y;

  l=16;
  i=l;
  v=n;
  y=i;

  
  /*@

    loop invariant 0 <= i && i <= 16;

    loop invariant v + i == n + 16;

    loop invariant y == 16 + (16 - i)*n + ((16 - i)*(17 - i))/2;

    loop assigns i, v, y;

    loop variant i;

  */
while (i>0) {
      v = v+1;
      y = y+v;
      i = i-1;
  }

}