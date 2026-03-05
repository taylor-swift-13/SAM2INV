int main152(int a){
  int l2w, nt, fp, di, i31, b, yh;

  l2w=60;
  nt=0;
  fp=0;
  di=0;
  i31=a;
  b=a;
  yh=nt;

  while (di<l2w) {
      fp = (fp+1)%5;
      di++;
      yh = (yh+di)%6;
      i31++;
      b = b + i31;
      a++;
  }

}
