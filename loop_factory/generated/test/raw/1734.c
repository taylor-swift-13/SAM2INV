int main1(int j){
  int x, x2, z5;

  x=j;
  x2=1;
  z5=0;

  while (x2<x) {
      z5++;
      x2 = 2*x2;
      j = j + z5;
  }

}
