int main1(int k){
  int b, y, v, j;

  b=63;
  y=3;
  v=y;
  j=y;

  while (y+3<=b) {
      if (v+4<=b) {
          v = v+4;
      }
      else {
          v = b;
      }
      v = v+j+j;
  }

}
