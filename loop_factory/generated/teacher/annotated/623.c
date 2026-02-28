int main1(int b,int p){
  int e, c, v, m, w;

  e=(b%10)+10;
  c=e;
  v=e;
  m=8;
  w=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == w;

  loop invariant c >= 0;
  loop invariant c <= e;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant e == (\at(b, Pre) % 10) + 10;
  loop invariant v + c == 2*e;
  loop invariant w == v;
  loop invariant m == 8 + (e - c)*e + (e - c)*(e - c + 1)/2;
  loop invariant c + v == 2*e;
  loop invariant 0 <= c;
  loop invariant e <= v;
  loop invariant v <= 2*e;
  loop invariant m == 8 + e*(v - e) + ((v - e) * (v - e + 1)) / 2;
  loop invariant c + v == 2 * ((b % 10) + 10);
  loop invariant c <= ((b % 10) + 10);
  loop invariant v == 2*e - c;
  loop invariant 0 <= c <= e;
  loop invariant w == 2*e - c;
  loop invariant m == 8 + (e - c)*e + ((e - c)*(e - c + 1))/2;
  loop invariant e == (b % 10) + 10;
  loop assigns v, m, w, c;
*/
while (c-1>=0) {
      v = v+1;
      m = m+v;
      w = w+1;
      c = c-1;
  }

}
