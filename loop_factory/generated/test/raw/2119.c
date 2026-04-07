int main1(){
  int za5q, su, lt, s, x;

  za5q=95;
  su=0;
  lt=1;
  s=0;
  x=1;

  while (su < za5q) {
      s += x;
      lt = lt*4+(s%5)+0;
      x += 2;
      su++;
  }

}
