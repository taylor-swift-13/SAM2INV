int main158(int i,int f,int b){
  int nd, ika, ju1, p2v, a2;

  nd=(f%7)+17;
  ika=1;
  ju1=0;
  p2v=-6;
  a2=-4;

  while (ika<=nd) {
      ju1 += 1;
      ika = 2*ika;
      p2v++;
      a2 = a2 + 1;
      b = b*4+(ika%5)+3;
      i = i*4+(ju1%2)+3;
  }

}
