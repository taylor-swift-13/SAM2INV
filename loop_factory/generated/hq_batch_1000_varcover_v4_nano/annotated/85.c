int main1(int a,int b,int p){
  int l, i, v, f, h;

  l=12;
  i=0;
  v=b;
  f=a;
  h=b;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant v == \at(b, Pre) + i;

    loop invariant f == \at(a, Pre) - i;

    loop invariant h == \at(b, Pre) + i*(i-1)/2;

    loop invariant l == 12;

    loop assigns v, f, h, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      f = f-1;
      h = h+i;
      i = i+1;
  }

}