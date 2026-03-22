int main1(int u){
  int kv, p;
  kv=51;
  p=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= p;
  loop invariant p <= kv;
  loop invariant kv == 51;
  loop assigns p;
*/
for (; p<=kv-1; p++) {
  }
}