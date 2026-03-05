int main144(int a,int b){
  int kd3, je, u7m, o0j, l;

  kd3=(b%31)+17;
  je=1;
  u7m=4;
  o0j=kd3;
  l=a;

  while (1) {
      if (!(je<=kd3-1)) {
          break;
      }
      u7m = u7m + o0j;
      o0j += l;
      je = je*3;
  }

}
