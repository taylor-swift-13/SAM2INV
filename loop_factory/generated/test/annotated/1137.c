int main1(int i){
  int ri, s, c, j, id;
  ri=(i%13)+10;
  s=0;
  c=0;
  j=-5;
  id=ri;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == s;
  loop invariant id == ri + s*(3 + i);
  loop invariant (s == 0) ==> (j == -5);
  loop invariant (s > 0) ==> (j == id - (i + 4));
  loop invariant s >= 0;
  loop assigns c, j, id, s;
*/
while (1) {
      c = c + 1;
      j = j + c;
      j = id+(-1);
      id = id + 3;
      id = id + i;
      s++;
      if (s>=ri) {
          break;
      }
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s >= 0;
  loop assigns s, c, id;
*/
while (id<j) {
      s++;
      c = c + s;
      id++;
  }
}