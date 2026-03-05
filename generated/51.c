int main51(int u){
  int b, y3c, z, v, hhuo, x;

  b=(u%10)+19;
  y3c=0;
  z=0;
  v=0;
  hhuo=2;
  x=b;

  while (1) {
      if (!(z<=b-1)) {
          break;
      }
      z = z + 7;
      if (z%3==0) {
          z += 1;
      }
      v++;
      x = x + y3c;
      u += 2;
      hhuo += v;
  }

}
