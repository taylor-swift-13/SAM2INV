int main1(){
  int a, v2i, mm, c, guq2;

  a=1;
  v2i=0;
  mm=-5;
  c=a;
  guq2=a;

  while (v2i+1<=a) {
      c = c/4;
      mm = mm*4;
      guq2 += mm;
      a = (v2i+1)-1;
  }

}
