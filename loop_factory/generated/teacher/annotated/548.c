int main1(int b,int p){
  int e, c, v, m;

  e=b+3;
  c=e;
  v=e;
  m=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == b + 3 && c == e && v >= e && v <= e + 1 && (m == 8 || m == -8);
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant m == 8 || m == -8;
  loop invariant v == e || v == e+1;
  loop invariant c == e;
  loop invariant e == b + 3;
  loop invariant e == b + 3 && c == e && (v == e || v == e + 1);
  loop assigns v, m;
*/
while (c-3>=0) {
      if (v+4<=e) {
          v = v+4;
      }
      else {
          v = e;
      }
      v = v+1;
      m = m+v;
      m = v-m;
  }

}
