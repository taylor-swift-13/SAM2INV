int main63(int a,int n,int p){
  int g, v, c, b, j;

  g=22;
  v=g+5;
  c=a;
  b=4;
  j=v;

  while (v-g>0) {
      c = c*2+3;
      b = b*c+3;
  }

  while (g<v) {
      c = c*3+5;
      j = j*c+5;
      c = c*3+2;
      j = j*c+2;
  }

  while (v-j>0) {
      c = c+1;
      g = g+c*c*c*c;
      g = g*g+g;
  }


  /*@ assert v-j <= 0; */
}
