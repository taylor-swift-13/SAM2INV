int main1(int b,int m,int n,int p){
  int e, t, x, i, v, o, w;

  e=p+7;
  t=e;
  x=6;
  i=2;
  v=-6;
  o=t;
  w=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == \at(p, Pre) + 7;
  loop invariant v == -6;
  loop invariant i <= 2;
  loop invariant p == \at(p, Pre);
  loop invariant e == p + 7;
  loop invariant x <= 6;

  loop invariant b == \at(b, Pre);
  loop invariant ((i == 2) && (x == 6)) || (i <= v);
  loop assigns i, x;
*/
while (1) {
      if (x>=e) {
          break;
      }
      if (v<=i) {
          i = v;
      }
      x = x+1;
      x = x+i;
      i = i+v;
  }

}
