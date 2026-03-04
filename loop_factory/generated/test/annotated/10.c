int main1(){
  int kv, m9c, p;
  kv=1;
  m9c=0;
  p=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= p;
  loop invariant p <= kv;
  loop invariant 0 <= m9c;
  loop invariant m9c < 12;
  loop invariant kv == 1;
  loop invariant m9c == 4*p;
  loop invariant p >= 0;
  loop invariant 0 <= p <= kv;
  loop invariant 0 <= m9c - 2*p <= 6;
  loop invariant m9c >= 0;
  loop invariant (p > 0) ==> ((m9c - 2*p) == 2 || (m9c - 2*p) == 6);
  loop assigns m9c, p;
*/
while (p<kv) {
      m9c = (m9c+1)%6;
      p++;
      m9c = m9c+p+p;
      m9c++;
  }
}