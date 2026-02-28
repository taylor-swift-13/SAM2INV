int main104(int b,int k,int p){
  int f, m, s, w, h;

  f=b+7;
  m=0;
  s=p;
  w=k;
  h=p;

  while (m<=f-5) {
      s = s+3;
      w = w+s;
      h = h+w;
      s = s+w+h;
      s = s+1;
  }


  /*@ assert m > f-5; */
}
