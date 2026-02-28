int main1(int k,int p){
  int l, c, a, u;

  l=57;
  c=0;
  a=0;
  u=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (a == 0) ==> (u == l);

  loop invariant (a == 0) || (a == l);
  loop invariant c <= l - 1;
  loop invariant c == 0;
  loop invariant 0 <= a;
  loop invariant a <= l;
  loop invariant -1 <= u;
  loop invariant u <= l + 2;
  loop invariant (a == l) || (a == 0 && u == l);
  loop invariant l == 57;
  loop invariant u >= 0;
  loop invariant 0 <= c;
  loop invariant c <= l;
  loop invariant c == 0 && a <= l && (a == 0 || a == 57) && u >= 0;
  loop assigns a, u;
*/
while (c+1<=l) {
      u = l-a;
      a = a+1;
      u = u-1;
      if ((c%9)==0) {
          a = a-c;
      }
      a = a+u;
      if ((c%9)==0) {
          u = u+3;
      }
  }

}
