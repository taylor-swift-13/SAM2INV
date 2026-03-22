int main1(){
  int e42e, ik, yyx, rczo, wtdz;

  e42e=(1%60)+60;
  ik=(1%9)+2;
  yyx=0;
  rczo=0;
  wtdz=10;

  while (e42e>ik*yyx+rczo) {
      if (rczo==ik-1) {
          rczo = 0;
          yyx += 1;
      }
      else {
          rczo += 1;
      }
      wtdz += yyx;
  }

}
