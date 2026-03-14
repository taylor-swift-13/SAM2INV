int main1(int g,int p){
  int ar81, c2, sc, k, qqa, x, fo;
  ar81=55;
  c2=0;
  sc=0;
  k=1;
  qqa=2;
  x=ar81;
  fo=13;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sc == k - 1;
  loop invariant g == \at(g, Pre);
  loop invariant qqa == sc + 2;
  loop invariant ar81 == 55;
  loop invariant x == ar81;
  loop invariant c2 == 0;
  loop invariant 5*fo - sc == 65;
  loop invariant sc >= 0;
  loop invariant fo  == 13 + sc/5;
  loop assigns k, g, qqa, sc, fo, p;
*/
while (1) {
      if (!(sc<=ar81-1)) {
          break;
      }
      k = k + 5;
      g = g + c2;
      qqa = qqa + 5;
      sc = sc + 5;
      fo = fo + 1;
      p = x+fo+g;
  }
}