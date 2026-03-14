int main1(int i){
  int i7y, e9, a, pk, n, g6d;

  i7y=i;
  e9=2;
  a=i7y;
  pk=5;
  n=0;
  g6d=4;

  while (e9<=i7y-1) {
      pk = pk+a*e9;
      g6d = g6d + pk;
      a = a+(pk%7);
      e9 = i7y;
  }

  while (1) {
      if (!(a*3<=pk)) {
          break;
      }
      g6d += n;
      e9 = e9+(g6d%9);
      n = n+(g6d%9);
      pk = (a*3)-1;
  }

}
